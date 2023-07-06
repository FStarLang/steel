module QuickSortConcurrent
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.FractionalPermission
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module R = Steel.ST.Reference
module Prf = Steel.ST.GenArraySwap.Proof
module SZ = FStar.SizeT

#set-options "--ide_id_info_off"
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"
#restart-solver

let nat_smaller (n: nat) = i:nat{i < n}
let seqn (n: nat) = (s:Seq.seq int{Seq.length s = n})
let arrayn (n: nat) = (a:A.array int{A.length a = n})
let nat_fits = n:nat{SZ.fits n}

let seq_swap (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)) =
  Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i)

type permutation (#a: Type): Seq.seq a -> Seq.seq a -> Type =
  | Refl : s: Seq.seq a -> permutation s s
  | Swap : s1: Seq.seq a -> s2: Seq.seq a -> i: nat_smaller (Seq.length s2) -> j: nat_smaller (Seq.length s2) ->
   permutation s1 s2 -> permutation s1 (seq_swap s2 i j)

let permutation_swap (#a: eqtype) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)):
  Lemma (permutation s (seq_swap s i j))
    [SMTPat (permutation s (seq_swap s i j))]
  = Squash.return_squash (Swap s s i j (Refl s))

let assert_prop (p: prop) : Pure unit (requires p) (ensures fun _ -> p) = ()
let assume_prop (p: prop) : Pure unit (requires True) (ensures fun _ -> p) = admit()

let rec compose_perm_aux (#a: eqtype) (s1 s2 s3: Seq.seq a) (#p12: permutation s1 s2) (#p23: permutation s2 s3):
  Tot (permutation s1 s3)
  (decreases p23)
  = match p23 with
  | Refl _ -> p12
  | Swap _ s4 i j p24 -> (
    assert (s3 = seq_swap s4 i j);
    let p14 = compose_perm_aux s1 s2 s4 #p12 #p24 in
    Swap s1 s4 i j p14)

let compose_permutations (#a:eqtype) (s1 s2 s3: Seq.seq a)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]
   = (let s12: squash (permutation s1 s2) = () in let s23: squash (permutation s2 s3) = () in
   Squash.bind_squash s12 (fun p12 -> Squash.bind_squash s23 (fun p23 -> Squash.return_squash (compose_perm_aux s1 s2 s3 #p12 #p23))))

let permutation_refl (#a:eqtype) (s: Seq.seq a)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]
   = Squash.return_squash (Refl s)

assume
val op_Array_Access
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
: stt t
    (requires
      A.pts_to_range a l r p s)
    (ensures fun res ->
      A.pts_to_range a l r p s `star`
      pure (Seq.length s == r - l /\
            res == Seq.index s (SZ.v i - l)))

assume
val op_Array_Assignment
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (v: t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  //(#s: Ghost.erased (Seq.seq t) {US.v i < Seq.length s})
  (#s0: Ghost.erased (Seq.seq t))
: stt unit
    //(requires A.pts_to a full_perm s)
    (requires A.pts_to_range a l r full_perm s0)
    //(ensures fun _ -> A.pts_to_range a l r full_perm (Seq.upd s0 (SZ.v i - l) v))
    //(ensures fun _ -> pure (Seq.length s0 == r - l) `star` A.pts_to a full_perm (Seq.upd s0 (SZ.v i - l) v))
    (ensures fun _ -> (exists_ (fun s -> A.pts_to_range a l r full_perm s `star`
    pure(
      Seq.length s0 == r - l /\ s == Seq.upd s0 (SZ.v i - l) v
    ))))

```pulse
fn swap (a: A.array int) (i j: nat_fits) (#l:(l:nat{l <= i /\ l <= j})) (#r:(r:nat{i < r /\ j < r}))
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a l r full_perm s0
  ensures exists s. (A.pts_to_range a l r full_perm s
    ** pure (Seq.length s0 = r - l /\ Seq.length s = r - l /\
      s = seq_swap s0 (i - l) (j - l) /\ permutation s0 s
    ))
{
  let vi = a.(SZ.uint_to_t i);
  let vj = a.(SZ.uint_to_t j);
  (a.(SZ.uint_to_t i) <- vj);
  (a.(SZ.uint_to_t j) <- vi);
  ()
}
```

let sorted_between (s: Seq.seq int) (a b: int)
  = forall (i j: nat). 0 <= i /\ a <= i /\ i < j /\ j <= b /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let same_between (n: nat) (s0 s: seqn n) (lo hi: int)
  = forall (k: nat). 0 <= k /\ lo <= k /\ k <= hi /\ k < n ==> Seq.index s0 k = Seq.index s k

//let between_bounds (n: nat) (s: seqn n) (lo hi: int) (lb rb: int)
//  = forall (k: nat). 0 <= k /\ lo <= k /\ k <= hi /\ k < n ==> lb <= Seq.index s k /\ Seq.index s k <= rb

//let between_bounds (n: nat) (s: seqn n) (lo hi: int) (lb rb: int)
//  = forall (k: nat). 0 <= k /\ lo <= k /\ k <= hi /\ k < n ==> lb <= Seq.index s k /\ Seq.index s k <= rb


```pulse
fn partition (a: A.array int) (lo: nat) (hi:(hi:nat{lo < hi})) (n: nat) (lb rb: int) (#s0: Ghost.erased (Seq.seq int))
  requires (
    A.pts_to_range a lo (hi + 1) full_perm s0 **
    pure (
      //0 <= hi /\
      hi < n /\
      //0 <= lo /\
      n = A.length a /\ SZ.fits n /\
      Seq.length s0 = hi + 1 - lo // /\
      //between_bounds n s0 lo hi lb rb
      )
  )
  returns r: int & int & int // left, right, pivot
  ensures exists s. (
    A.pts_to_range a lo (hi + 1) full_perm s
     **
    pure (
      Seq.length s = hi + 1 - lo /\ Seq.length s0 = hi + 1 - lo
      /\ lo <= r._1 /\ r._1 <= r._2 /\ r._2 <= hi /\ hi < n
      /\ (forall (k: nat). lo <= k /\ k < r._1 ==> Seq.index s (k - lo) < r._3)
      /\ (forall (k: nat). r._1 <= k /\ k <= r._2 ==> Seq.index s (k - lo) == r._3)
      /\ (forall (k: nat). r._2 + 1 <= k /\ k <= hi ==> Seq.index s (k - lo) > r._3)
      ///\ same_between n s0 s 0 (lo - 1) /\ same_between n s0 s (hi + 1) (n - 1)
      ///\ between_bounds n s lo hi lb rb
      /\ permutation s0 s
   ))
{
  let pivot = a.(SZ.uint_to_t hi);
  let mut i = lo - 1;
  let mut j = lo - 1;
  let mut k = lo;
  while (let vk = !k; (vk < hi))
    invariant b . exists s vi vj vk. (
      A.pts_to_range a lo (hi + 1) full_perm s **
      R.pts_to i full_perm vi **
      R.pts_to j full_perm vj **
      R.pts_to k full_perm vk **
      pure (
        eq2_prop #bool b (vk < hi) /\
        lo <= vk /\ vk <= hi /\
        lo - 1 <= vi /\ vi <= vj /\ vj < vk /\
        Seq.length s = hi + 1 - lo /\
        Seq.index s (hi - lo) = pivot
        /\ (forall (l:nat). lo <= l /\ l <= vi ==> Seq.index s (l - lo) < pivot)
        /\ (forall (l:nat). vi + 1 <= l /\ l <= vj ==> Seq.index s (l - lo) == pivot)
        /\ (forall (l:nat). vj + 1 <= l /\ l <= vk - 1 ==> Seq.index s (l - lo) > pivot)
        /\ permutation s0 s
        (*
        A.length a = n
        /\ same_between n s0 s 0 (lo - 1) /\ same_between n s0 s (hi + 1) (n - 1)
        /\ between_bounds n s lo hi lb rb *)
      ))
  {
    let vk = !k;
    let ak = a.(SZ.uint_to_t vk);
    if (ak < pivot) {
      let vi = !i;
      i := vi + 1;
      let vj = !j;
      j := vj + 1;
      swap a (vj + 1) vk;
      swap a (vi + 1) (vj + 1);
      k := vk + 1;
      ()
    }
    else {
      if (ak = pivot) {
        let vj = !j;
        j := vj + 1;
        swap a (vj + 1) vk;
        k := vk + 1;
        ()
      }
      else {
        k := vk + 1;
        ()
      };
    };
  };

  let vj = !j;
  j := vj + 1;

  // swap j with hi
  swap a (vj + 1) hi;

  let vi = !i;
  i := vi + 1;
  let vi' = vi + 1;
  let vj' = vj + 1;
  (vi', vj', pivot)
}
```
(*

```pulse
fn partition_old (a: A.array int) (lo hi: int) (n: nat) (lb rb: int) (#s0: Ghost.erased (Seq.seq int))
  requires (
    A.pts_to a full_perm s0 **
    pure (
      0 <= hi /\ hi < n /\
      0 <= lo /\ lo < hi /\
      n = A.length a /\ SZ.fits n /\
      n = Seq.length s0
      /\ between_bounds n s0 lo hi lb rb
      )
  )
  returns p: nat
  ensures exists s. (
    A.pts_to a full_perm s **
    pure (
      Seq.length s = n /\ Seq.length s0 = n /\ A.length a = n
      /\ lo <= p /\ p <= hi
      /\ p < n /\ hi < n
      /\ (forall (k: nat). lo <= k /\ k <= p ==> Seq.index s k <= Seq.index s p)
      /\ (forall (k: nat). p + 1 <= k /\ k <= hi ==> Seq.index s k > Seq.index s p)
      /\ same_between n s0 s 0 (lo - 1) /\ same_between n s0 s (hi + 1) (n - 1)
      /\ between_bounds n s lo hi lb rb
      /\ permutation s0 s
    )
   )
{
  let pivot = a.(SZ.uint_to_t hi);
  let mut i = lo - 1;
  let mut j = lo;
  while (let vj = !j; (vj < hi))
    invariant b . exists s vi vj. (
      A.pts_to a full_perm s **
      R.pts_to i full_perm vi **
      R.pts_to j full_perm vj **
      pure (
        eq2_prop #bool b (vj < hi) /\
        lo <= vj /\ vj <= hi /\
        lo - 1 <= vi /\ vi < vj /\
        A.length a = n /\
        n = Seq.length s0
        /\ n = Seq.length s
        /\ Seq.index s hi = pivot
        /\ (forall (k:nat). lo <= k /\ k <= vi ==> Seq.index s k <= pivot)
        /\ (forall (k:nat). vi + 1 <= k /\ k <= vj - 1 ==> Seq.index s k > pivot)
        /\ same_between n s0 s 0 (lo - 1) /\ same_between n s0 s (hi + 1) (n - 1)
        /\ between_bounds n s lo hi lb rb
        /\ permutation s0 s
      ))
  {
    let vj = !j;
    let aj = a.(SZ.uint_to_t vj);
    if (aj <= pivot) {
      let vi = !i;
      i := vi + 1;
      swap n a (vi + 1) vj;
      j := vj + 1;
      ()
    }
    else {
      j := vj + 1;
      ()
    };
  };
  let vi_old = !i;
  i := vi_old + 1;
  let vi = !i;
  swap n a vi hi;
  vi
}
```

```pulse
fn quicksort' (a: A.array int) (lo hi: int) (lb rb: int) (n: nat) (#s0: (s0:Ghost.erased (Seq.seq int){Seq.length s0 = n}))
  requires A.pts_to a full_perm s0 ** pure (
    0 <= lo /\ hi < n /\ Seq.length s0 = n /\ SZ.fits n /\ A.length a = n
    /\ hi >= -1 /\ lo <= n /\ lb <= rb
    /\ between_bounds n s0 lo hi lb rb
    )
  ensures exists s. (
    A.pts_to a full_perm s ** pure (
      0 <= lo /\ hi < n /\ Seq.length s0 = n /\ Seq.length s = n /\ SZ.fits n /\ A.length a = n
      /\ same_between n s0 s 0 (lo - 1) /\ same_between n s0 s (hi + 1) (n - 1)
      /\ sorted_between s lo hi
      /\ between_bounds n s lo hi lb rb
      /\ permutation s0 s
    )
  )
{ admit() }
```

```pulse
fn quicksort (a: A.array int) (lo hi: int) (lb rb: int) (n: nat) (#s0: (s0:Ghost.erased (Seq.seq int){Seq.length s0 = n}))
  requires A.pts_to a full_perm s0 ** pure (
    0 <= lo /\ hi < n /\ Seq.length s0 = n /\ SZ.fits n /\ A.length a = n
    /\ hi >= -1 /\ lo <= n /\ lb <= rb
    /\ between_bounds n s0 lo hi lb rb
    )
  ensures exists s. (
    A.pts_to a full_perm s ** pure (
      0 <= lo /\ hi < n /\ Seq.length s0 = n /\ Seq.length s = n /\ SZ.fits n /\ A.length a = n
      /\ same_between n s0 s 0 (lo - 1) /\ same_between n s0 s (hi + 1) (n - 1)
      /\ sorted_between s lo hi
      /\ between_bounds n s lo hi lb rb
      /\ permutation s0 s
    )
  )
  // decreases hi - lo (>= -2n)
{
  if (lo < hi)
  {
    let r = partition a lo hi n lb rb;
    let pivot = r._3;

    // termination check
    assert_prop (hi - lo > (r._1 - 1) - lo);
    quicksort' a lo (r._1 - 1) lb pivot n;

    // termination check
    assert_prop (hi - lo > hi - (r._2 + 1));
    quicksort' a (r._2 + 1) hi pivot rb n;
    ()
  }
  else {
    ()
  }
}
```
*)