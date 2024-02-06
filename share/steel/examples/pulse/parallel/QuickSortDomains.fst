module QuickSortDomains

open Steel.ST.Util

open Pulse.Lib.Pervasives
open Domains

module T = FStar.Tactics
module PM = Pulse.Main
module U32 = FStar.UInt32
module A = Pulse.Lib.Array
module Prf = Steel.ST.GenArraySwap.Proof
module SZ = FStar.SizeT

open Promises
//open Seq.Properties

assume
val pts_to_range
  (#elt: Type0) (a: array elt) (i j: nat)
  (p: perm)
  ([@@@ smt_fallback ] s: Seq.seq elt)
  //(s: Seq.seq elt)
: Tot vprop

assume
val pts_to_range_intro
  (#elt: Type0) (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
: stt_ghost unit emp_inames
    (A.pts_to a #p s)
    (fun _ -> pts_to_range a 0 (length a) p s)

assume
val pts_to_range_elim
  (#elt: Type0) (a: A.array elt)
  (p: perm)
  (s: Seq.seq elt)
: stt_ghost unit emp_inames
    (pts_to_range a 0 (length a) p s)
    (fun _ -> A.pts_to a #p s)

assume
val pts_to_range_split
  (#elt: Type0)
  (a: A.array elt)
  (i m j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
: stt_ghost unit emp_inames
    (pts_to_range a i j p s **
      pure (i <= m /\ m <= j)
    )
    (fun _ -> exists_ (fun s1 -> exists_ (fun s2 ->
      pts_to_range a i m p s1 **
      pts_to_range a m j p s2 **
      pure (
        i <= m /\ m <= j /\ j <= A.length a /\
        Seq.length s == j - i /\
        s1 == Seq.slice s 0 (m - i) /\
        s2 == Seq.slice s (m - i) (Seq.length s) /\
        s == Seq.append s1 s2
    ))))

assume
val pts_to_range_join
  (#elt: Type0)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s1 #s2: Seq.seq elt)
: stt_ghost unit emp_inames
    (pts_to_range a i m p s1 ** pts_to_range a m j p s2)
    (fun _ -> pts_to_range a i j p (s1 `Seq.append` s2))

assume
val pts_to_range_index
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
: stt t
    (requires
      pts_to_range a l r p s)
    (ensures fun res ->
      pts_to_range a l r p s **
      pure (Seq.length s == r - l /\
            res == Seq.index s (SZ.v i - l)))

assume
val pts_to_range_upd
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (v: t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  //(#s: Ghost.erased (Seq.seq t) {US.v i < Seq.length s})
  (#s0: Ghost.erased (Seq.seq t))
: stt unit
    //(requires A.pts_to a full_perm s)
    (requires pts_to_range a l r full_perm s0)
    //(ensures fun _ -> pts_to_range a l r full_perm (Seq.upd s0 (US.v i - l) v))
    //(ensures fun _ -> pure (Seq.length s0 == r - l) ** A.pts_to a full_perm (Seq.upd s0 (US.v i - l) v))
    (ensures fun _ -> (exists_ (fun s -> pts_to_range a l r full_perm s **
    pure(
      Seq.length s0 == r - l /\ s == Seq.upd s0 (SZ.v i - l) v
    ))))


let nat_smaller (n: nat) = i:nat{i < n}
let seqn (n: nat) = (s:Seq.seq int{Seq.length s = n})
let arrayn (n: nat) = (a:A.array int{A.length a = n})
let nat_fits = n:nat{SZ.fits n}

let seq_swap (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)) =
  Seq.swap s j i

let larger_than (s: Seq.seq int) (lb: int)
  = forall (k: nat). k < Seq.length s ==> lb <= Seq.index s k

let larger_than_slice (s: Seq.seq int) (lo: nat) (hi: nat{lo <= hi /\ hi <= Seq.length s}) (lb: int):
  Lemma (requires larger_than s lb)
  (ensures larger_than (Seq.slice s lo hi) lb)
  //[SMTPat (larger_than (Seq.slice s lo hi) lb)]
= ()

let smaller_than (s: Seq.seq int) (rb: int)
  = forall (k: nat). k < Seq.length s ==> Seq.index s k <= rb

let between_bounds (s: Seq.seq int) (lb rb: int)
  = larger_than s lb /\ smaller_than s rb

[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int): prop
//let between_bounds (s: Seq.seq int) (lb rb: int)
= Seq.Properties.permutation int s1 s2

let append_permutations_3 (s1 s2 s3 s1' s3': Seq.seq int):
  Lemma
    (requires permutation s1 s1' /\ permutation s3 s3')
    (ensures permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')))
= (
  reveal_opaque (`%permutation) (permutation s1 s1');
  reveal_opaque (`%permutation) (permutation s2 s2);
  reveal_opaque (`%permutation) (permutation s3 s3');
  Seq.Properties.append_permutations s2 s3 s2 s3';
  reveal_opaque (`%permutation) (permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')));
  Seq.Properties.append_permutations s1 (Seq.append s2 s3) s1' (Seq.append s2 s3')
  )

let seq_swap_commute (s: Seq.seq int) (i j: nat_smaller (Seq.length s)):
  Lemma (seq_swap s i j == seq_swap s j i)
  = (
    let sij = seq_swap s i j in
    let sji = seq_swap s j i in
    assert (Seq.length sij = Seq.length sji);
    assert (forall (k:nat{k < Seq.length sij}). (Seq.index sij k == Seq.index sji k));
    Seq.lemma_eq_elim sij sji;
    ()
  )

let permutation_swap (s: Seq.seq int) (i j: nat_smaller (Seq.length s)):
  Lemma (permutation s (seq_swap s i j))
    [SMTPat (permutation s (seq_swap s i j))]
    = (
      reveal_opaque (`%permutation) (permutation s (seq_swap s i j));
      if i <= j
        then (Seq.Properties.lemma_swap_permutes s i j; seq_swap_commute s i j)
        else Seq.Properties.lemma_swap_permutes s j i)

let assert_prop (p: prop) : Pure unit (requires p) (ensures fun _ -> p) = ()

let compose_permutations (s1 s2 s3: Seq.seq int)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]
   = (
      reveal_opaque (`%permutation) (permutation s1 s2);
      reveal_opaque (`%permutation) (permutation s2 s3);
      reveal_opaque (`%permutation) (permutation s1 s3);
      Seq.perm_len s1 s2;
      Seq.perm_len s1 s3;
      Seq.lemma_trans_perm s1 s2 s3 0 (Seq.length s1);
      ()
   )

let permutation_refl (s: Seq.seq int)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]
   =
   (
      reveal_opaque (`%permutation) (permutation s s);
      ()
   )

let op_Array_Access
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
: stt t
    (requires
      pts_to_range a l r p s)
    (ensures fun res ->
      pts_to_range a l r p s **
      pure (Seq.length s == r - l /\
            res == Seq.index s (SZ.v i - l)))
= pts_to_range_index a i #l #r #s #p

let op_Array_Assignment
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (v: t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  //(#s: Ghost.erased (Seq.seq t) {US.v i < Seq.length s})
  (#s0: Ghost.erased (Seq.seq t))
: stt unit
    (requires pts_to_range a l r full_perm s0)
    (ensures fun _ -> (exists_ (fun s -> pts_to_range a l r full_perm s **
    pure(
      Seq.length s0 == r - l /\ s == Seq.upd s0 (SZ.v i - l) v
    ))))
= pts_to_range_upd a i v #l #r

```pulse
fn swap (a: A.array int) (i j: nat_fits) (#l:(l:nat{l <= i /\ l <= j})) (#r:(r:nat{i < r /\ j < r}))
  (#s0: Ghost.erased (Seq.seq int))
  requires pts_to_range a l r full_perm s0
  ensures exists s. (pts_to_range a l r full_perm s
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

let sorted (s: Seq.seq int)
  = forall (i j: nat). 0 <= i /\ i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let to_nat (x: int{x >= 0}): nat = x

#push-options "--z3rlimit 30"
```pulse
fn partition (a: A.array int) (lo: nat) (hi:(hi:nat{lo < hi - 1})) (n: nat) (lb rb: int) (#s0: Ghost.erased (Seq.seq int))
  requires (
    pts_to_range a lo hi full_perm s0 **
    pure (
      hi - 1 < n /\
      n = A.length a /\ SZ.fits n /\
      Seq.length s0 = hi - lo /\
      between_bounds s0 lb rb
      )
  )
  returns r: nat & nat & int // left, right, pivot
  ensures exists s. (
    pts_to_range a lo hi full_perm s
     **
    pure (
      Seq.length s = hi - lo /\ Seq.length s0 = hi - lo
      /\ lo <= r._1 /\ r._1 < r._2 /\ r._2 <= hi /\ hi - 1 < n
      /\ lb <= r._3 /\ r._3 <= rb
      /\ (forall (k: nat). k < r._1 - lo ==> Seq.index s k < r._3)
      /\ (forall (k: nat). r._1 - lo <= k /\ k <= r._2 - 1 - lo ==> Seq.index s k == r._3)
      /\ (forall (k: nat). r._2 - lo <= k /\ k <= hi - 1 - lo ==> Seq.index s k > r._3)
      /\ between_bounds s lb rb
      /\ permutation s0 s
   ))
{
  let pivot = a.(SZ.uint_to_t (hi - 1));
  let mut i = lo - 1;
  let mut j = lo - 1;
  let mut k = lo;
  while (let vk = !k; (vk < hi - 1))
    invariant b . exists s vi vj vk. (
      pts_to_range a lo hi full_perm s **
      pts_to i vi **
      pts_to j vj **
      pts_to k vk **
      pure (
        b == (vk < hi - 1) /\
        lo <= vk /\ vk <= hi - 1 /\
        lo - 1 <= vi /\ vi <= vj /\ vj < vk /\
        lb <= pivot /\ pivot <= rb /\
        Seq.length s = hi - lo /\
        Seq.index s (hi - 1 - lo) = pivot
        /\ (forall (l:nat). 0 <= l /\ l <= vi - lo ==> Seq.index s l < pivot)
        /\ (forall (l:nat). vi + 1 - lo <= l /\ l <= vj - lo ==> Seq.index s l == pivot)
        /\ (forall (l:nat). vj + 1 - lo <= l /\ l <= vk - 1 - lo ==> Seq.index s l > pivot)
        /\ permutation s0 s
        /\ between_bounds s lb rb
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
  swap a (vj + 1) (hi - 1);

  let vi = !i;
  i := vi + 1;
  let vi' = to_nat (vi + 1);
  let vj' = to_nat (vj + 2);
  (vi', vj', pivot)
}
```
#pop-options

assume
val split
  (#elt: Type)
  (a: A.array elt)
  (i: nat)
  (#l #r: nat)
  (#s: Ghost.erased (Seq.seq elt))
  (#p: perm)
: stt unit
    (requires pts_to_range a l r p s
     ** pure (l <= i /\ i <= r))
    (ensures fun _ ->
      exists_ (fun s1 -> exists_ (fun s2 ->
        pts_to_range a l i p s1 **
        pts_to_range a i r p s2 ** pure (
          l <= i /\ i <= r /\
          Seq.length s == r - l /\
          Seq.length s1 == i - l /\ Seq.length s2 == r - i /\
          s1 == Seq.slice s 0 (i - l) /\
          s2 == Seq.slice s (i - l) (Seq.length s) /\
          s == Ghost.hide (Seq.append s1 s2))
        )))

let transfer_larger_slice (s: Seq.seq int) (l: nat) (r: nat{l <= r /\ r <= Seq.length s}) (lb: int):
  Lemma
    (requires (forall (k: nat). l <= k /\ k < r ==> (lb <= Seq.index s k)))
    (ensures larger_than (Seq.slice s l r) lb)
= ()

let transfer_smaller_slice (s: Seq.seq int) (l: nat) (r: nat{l <= r /\ r <= Seq.length s}) (rb: int):
  Lemma
    (requires (forall (k: nat). l <= k /\ k < r ==> (Seq.index s k <= rb)))
    (ensures smaller_than (Seq.slice s l r) rb)
= ()

#push-options "--z3rlimit 30"
```pulse
fn partition_wrapper (a: A.array int) (lo: nat) (hi:(hi:nat{lo < hi - 1})) (n: nat) (lb rb: int) (#s0: Ghost.erased (Seq.seq int))
  requires (
    pts_to_range a lo hi full_perm s0 **
    pure (hi - 1 < n /\ n = A.length a /\ SZ.fits n /\ between_bounds s0 lb rb
      /\ Seq.length s0 = hi - lo)
  )
  returns r: nat & nat & int // left, right, pivot
  ensures exists s1 s2 s3. (
    pts_to_range a lo r._1 full_perm s1 **
    pts_to_range a r._1 r._2 full_perm s2 **
    pts_to_range a r._2 hi full_perm s3 **
    pure (
      lo <= r._1 /\ r._1 < r._2 /\ r._2 <= hi /\ hi - 1 < n /\
      lb <= r._3 /\ r._3 <= rb /\
      Seq.length s1 = r._1 - lo /\ Seq.length s2 = r._2 - r._1 /\ Seq.length s3 = hi - r._2
      /\ between_bounds s1 lb r._3
      /\ between_bounds s2 r._3 r._3
      /\ between_bounds s3 r._3 rb
      /\ permutation s0 (Seq.append s1 (Seq.append s2 s3))
   ))
{
  (*
  let r = partition a lo hi n lb rb #s0;
  with s. assert (pts_to_range a lo hi full_perm s);

  transfer_smaller_slice s 0 (r._1 - lo) r._3;
  transfer_larger_slice s (r._2 - lo) (hi - lo) r._3;

  let pivot = r._3;
  split a r._1;
  with s1. assert (pts_to_range a lo r._1 full_perm s1);
  assert_prop (s1 == Seq.slice s 0 (r._1 - lo));

  assert_prop (between_bounds s1 lb r._3);

  with s23. assert (pts_to_range a r._1 hi full_perm s23);
  assert_prop (s23 == Seq.slice s (r._1 - lo) (Seq.length s));

  assert (pts_to_range a lo r._1 full_perm s1);
  split a r._2 #(r._1);

  with s2. assert (pts_to_range a r._1 r._2 full_perm s2);
  assert_prop (s2 == Seq.slice s23 0 (r._2 - r._1));
  assert_prop (s2 == Seq.slice s (r._1 - lo) (r._2 - lo));
  with s3. assert (pts_to_range a r._2 hi full_perm s3);
  assert_prop (s3 == Seq.slice s (r._2 - lo) (hi - lo));
  assert_prop (Seq.length s1 = r._1 - lo);
  assert_prop (Seq.length s2 = r._2 - r._1);
  assert_prop (Seq.length s3 = hi - r._2);
  assert_prop (s == Seq.append s1 (Seq.append s2 s3));
  r
  *)
  admit()
}
```
#pop-options

assume
val join
  (#elt: Type)
  (a: A.array elt)
  //(i: nat)
  (l m r: nat)
  (#s1 #s2: Ghost.erased (Seq.seq elt))
  (#p: perm)
: stt unit
    (requires pts_to_range a l m p s1 ** pts_to_range a m r p s2)
    (ensures fun _ -> pts_to_range a l r p (Seq.append s1 s2))   

unfold
let pure_pre_quicksort (a: A.array int) (lo: nat) (hi:(hi:int{-1 <= hi - 1 /\ lo <= hi})) (lb rb: int) (n: nat) (s0: Seq.seq int)
  = hi - 1 < n /\ between_bounds s0 lb rb /\ Seq.length s0 = hi - lo /\ SZ.fits n /\ A.length a = n /\ lo <= n /\ lb <= rb

unfold
let pure_post_quicksort (a: A.array int) (lo: nat) (hi:(hi:int{-1 <= hi - 1 /\ lo <= hi})) (lb rb: int) (n: nat) (s0 s: Seq.seq int)
  = hi - 1 < n /\ Seq.length s0 = hi - lo /\ Seq.length s = hi - lo /\ SZ.fits n /\ A.length a = n
      /\ sorted s /\ between_bounds s lb rb /\ permutation s0 s

```pulse
fn quicksort' (a: A.array int) (lo: nat)
(hi:(hi:int{-1 <= hi - 1 /\ lo <= hi}))
(lb rb: int) (n: nat) (#s0: Ghost.erased (Seq.seq int))
  requires pts_to_range a lo hi full_perm s0 ** pure (pure_pre_quicksort a lo hi lb rb n s0)
  ensures exists s. (pts_to_range a lo hi full_perm s ** pure (pure_post_quicksort a lo hi lb rb n s0 s))
{ admit() }
```

let pre_quicksort a lo hi lb rb n s0 p f: vprop
 = (pts_to_range a lo hi full_perm s0 ** pure (pure_pre_quicksort a lo hi lb rb n s0)
  ** pool_alive f p)

let post_quicksort a lo hi lb rb n s0 p f (_: unit): vprop
= (exists_ (fun s -> (pts_to_range a lo hi full_perm s ** pure (pure_post_quicksort a lo hi lb rb n s0 s))
** promise (pool_done p) (pool_alive f p)))



assume val quicksort_funct (a: A.array int) (lo: nat)
(hi:(hi:int{-1 <= hi - 1 /\ lo <= hi}))
(lb rb: int) (n: nat) (#s0: Ghost.erased (Seq.seq int))
(#p: pool) (#f: perm)
(_: unit):
stt unit
(pre_quicksort a lo hi lb rb n s0 p f)
//(pts_to_range a lo hi full_perm s0 ** pure (pure_pre_quicksort a lo hi lb rb n s0))
//(fun () -> exists_ (fun s -> (pts_to_range a lo hi full_perm s ** pure (pure_post_quicksort a lo hi lb rb n s0 s))))
(post_quicksort a lo hi lb rb n s0 p f)

//#push-options "--print_universes --print_implicits"

let spawn_quicksort_rec
(a: A.array int) (lo: nat)
(hi:(hi:int{-1 <= hi - 1 /\ lo <= hi}))
(lb rb: int) (n: nat) (s0: Ghost.erased (Seq.seq int))
  //(#pre: vprop) (#post: unit -> vprop)
  (p: pool)
  (f1 f2: perm)
  //(funct: stt_funct unit pre post)
: stt u#0 (handler p unit (post_quicksort a lo hi lb rb n s0 p f2))
(pool_alive f1 p ** pre_quicksort a lo hi lb rb n s0 p f2)
(fun h -> pool_alive f1 p ** active h)
= spawn p (quicksort_funct a lo hi lb rb n #s0 #p #f2) #f1
 



//assume val assume_prop (p: prop): stt_ghost unit emp_inames emp (fun () -> pure p)
assume val combine_posts
  (a: A.array int)
  (lo: nat) 
  (m:int{-1 <= m - 1 /\ lo <= m})
  (hi:int{-1 <= hi - 1 /\ m <= hi})
  (lb mb rb: int)
  (n: nat)
  (#s0: Ghost.erased (Seq.seq int))
  (#s1: Ghost.erased (Seq.seq int))
  (p: pool)
  (f0 f1: perm)
: stt_ghost unit emp_inames
(post_quicksort a lo m lb mb n s0 p f0 () ** post_quicksort a m hi mb rb n s1 p f1 ())
(fun () -> post_quicksort a lo hi lb rb n (Seq.append s0 s1) p (sum_perm f0 f1) ())

```pulse
ghost fn
combine_promises_posts
  (a: A.array int)
  (lo: nat) 
  (m:(m:int{-1 <= m - 1 /\ lo <= m}))
  (hi:(hi:int{-1 <= hi - 1 /\ m <= hi}))
  (lb mb rb: int)
  (n: nat)
  (#s0: Ghost.erased (Seq.seq int))
  (#s1: Ghost.erased (Seq.seq int))
  (p: pool)
  (f0 f1: perm)
requires promise (pool_done p) (post_quicksort a lo m lb mb n s0 p f0 ())
  ** promise (pool_done p) (post_quicksort a m hi mb rb n s1 p f1 ())
ensures promise (pool_done p)
  (post_quicksort a lo hi lb rb n (Seq.append s0 s1) p (sum_perm f0 f1) ())
{
  join_promise #(pool_done p)
    (post_quicksort a lo m lb mb n s0 p f0 ())
    (post_quicksort a m hi mb rb n s1 p f1 ());

  rewrite_promise #(pool_done p)
    (post_quicksort a lo m lb mb n s0 p f0 () ** post_quicksort a m hi mb rb n s1 p f1 ())
    (post_quicksort a lo hi lb rb n (Seq.append s0 s1) p (sum_perm f0 f1) ())
    (fun () -> combine_posts a lo m hi lb mb rb n #s0 #s1 p f0 f1);

  ()
}
```



 
#push-options "--z3rlimit 10"

//let third (f: perm)

```pulse
fn quicksort
  (a: A.array int)
  (lo: nat) (hi:(hi:int{-1 <= hi - 1 /\ lo <= hi}))
  (lb rb: int)
  (n: nat)
  (p: pool)
  (f: perm)
  (#s0: Ghost.erased (Seq.seq int))
  requires pts_to_range a lo hi full_perm s0 ** pure (pure_pre_quicksort a lo hi lb rb n s0)
   ** pool_alive f p
  ensures exists s. (pts_to_range a lo hi full_perm s ** pure (pure_post_quicksort a lo hi lb rb n s0 s))
    ** promise (pool_done p) (pool_alive f p)
  // decreases hi + 1 - lo
{
  if (lo < hi - 1)
  {
    let r = partition_wrapper a lo hi n lb rb;
   with s1 s2 s3. assert (
    pts_to_range a lo r._1 full_perm s1 **
    pts_to_range a r._1 r._2 full_perm s2 **
    pts_to_range a r._2 hi full_perm s3);
 

(*
    with s1 s2 s3. assert (pts_to_range a lo r._1 full_perm s1 **
    pts_to_range a r._1 r._2 full_perm s2 ** pts_to_range a r._2 hi full_perm s3
    ** pure (permutation s0 (Seq.append s1 (Seq.append s2 s3))));
    *)

(*
 assert (exists s1 s2 s3. (
    pts_to_range a lo r._1 full_perm s1 **
    pts_to_range a r._1 r._2 full_perm s2 **
    pts_to_range a r._2 hi full_perm s3 **
    pure (
      lo <= r._1 /\ r._1 < r._2 /\ r._2 <= hi /\ hi - 1 < n /\
      lb <= r._3 /\ r._3 <= rb /\
      Seq.length s1 = r._1 - lo /\ Seq.length s2 = r._2 - r._1 /\ Seq.length s3 = hi - r._2
      /\ between_bounds s1 lb r._3
      /\ between_bounds s2 r._3 r._3
      /\ between_bounds s3 r._3 rb
      /\ permutation s0 (Seq.append s1 (Seq.append s2 s3))
   )));
   with s1 s2 s3. assert (
    pts_to_range a lo r._1 full_perm (reveal s1) **
    pts_to_range a r._1 r._2 full_perm (reveal s2) **
    pts_to_range a r._2 hi full_perm (reveal s3) **
    pure (
      lo <= r._1 /\ r._1 < r._2 /\ r._2 <= hi /\ hi - 1 < n /\
      lb <= r._3 /\ r._3 <= rb /\
      Seq.length s1 = r._1 - lo /\ Seq.length s2 = r._2 - r._1 /\ Seq.length s3 = hi - r._2
      /\ between_bounds s1 lb r._3
      /\ between_bounds s2 r._3 r._3
      /\ between_bounds s3 r._3 rb
      /\ permutation s0 (Seq.append s1 (Seq.append s2 s3))
   ));
   assert (
    (*
    pts_to_range a lo r._1 full_perm (reveal s1) **
    pts_to_range a r._1 r._2 full_perm (reveal s2) **
    pts_to_range a r._2 hi full_perm (reveal s3) **
    *)
    pure (
      lo <= r._1 /\ r._1 < r._2 /\ r._2 <= hi /\ hi - 1 < n /\
      lb <= r._3 /\ r._3 <= rb /\
      Seq.length s1 = r._1 - lo /\ Seq.length s2 = r._2 - r._1 /\ Seq.length s3 = hi - r._2
      /\ between_bounds s1 lb r._3
      /\ between_bounds s2 r._3 r._3
      /\ between_bounds s3 r._3 rb
      /\ permutation s0 (Seq.append s1 (Seq.append s2 s3))
   ));
  assert (pure (
      between_bounds s1 lb r._3 /\
      between_bounds s2 r._3 r._3
      /\ between_bounds s3 r._3 rb
      /\ permutation s0 (Seq.append s1 (Seq.append s2 s3))
   ));
  assert (pure (
      between_bounds s2 r._3 r._3
      /\ between_bounds s3 r._3 rb
      /\ permutation s0 (Seq.append s1 (Seq.append s2 s3))
   ));
  assert (pure (between_bounds s3 r._3 rb /\ permutation s0 (Seq.append s1 (Seq.append s2 s3))));
  assert (pure (
    permutation (reveal s0) (Seq.append (reveal s1) (Seq.append (reveal s2) (reveal s3)))
    /\ between_bounds s3 r._3 rb));
    *)
  assert (pure (permutation s0 (Seq.append s1 (Seq.append s2 s3))));
  //assert (pure (
   // permutation s0 (Seq.append s1 (Seq.append s2 s3))));



  //assert (pure (permutation s0 (Seq.append s1 (Seq.append s2 s3))));
  //assert (pure (Seq.Properties.permutation int s0 (Seq.append s1 (Seq.append s2 s3))));
 
 
 
 
    //assert (pure (permutation s0 (Seq.append s1 (Seq.append s2 s3))));
   //Seq.append_assoc s1 s2 s3;
   //assert (pure (permutation s0 (Seq.append s1 (Seq.append s2 s3))));
 
    //)));



    //assert (exists s1 s2 s3. pts_to_range a lo r._1 full_perm s1 **
    //pts_to_range a r._1 r._2 full_perm s2 ** pts_to_range a r._2 hi full_perm s3
    //** pure (permutation s0 (Seq.append s1 (Seq.append s2 s3))));
 
    let pivot = r._3;

      //assert (pure (permutation s0 (Seq.append s1 (Seq.append s2 s3))));
    //with s1 s2 s3. assert (pts_to_range a lo r._1 full_perm s1 **
    //pts_to_range a r._1 r._2 full_perm s2 ** pts_to_range a r._2 hi full_perm s3);
    //** pure (permutation s0 (Seq.append s1 (Seq.append s2 s3))));
    //assert_prop (squash (permutation s0 (Seq.append s1 (Seq.append s2 s3))));

    if (lo < hi + 1000) // worth parallelizing
    {


      let ff = half_perm f;
      let fff = half_perm ff;
      rewrite (pool_alive f p) as (pool_alive (sum_perm ff ff) p);
        //(sum_perm fff fff)) p);
      share_pool_alive p ff ff;

      fold (pre_quicksort a lo r._1 lb pivot n s1 p ff);
      let h1 = spawn_quicksort_rec a lo r._1 lb pivot n s1 p ff ff;
      assert (active h1);
      get_promise h1;
      assert promise (pool_done p) (post_quicksort a lo r._1 lb pivot n s1 p ff ());


      rewrite (pool_alive ff p) as (pool_alive (sum_perm fff fff) p);
      share_pool_alive p fff fff;
      fold (pre_quicksort a r._2 hi pivot rb n s3 p fff);
      let h2 = spawn_quicksort_rec a r._2 hi pivot rb n s3 p fff fff;
      get_promise h2;
      assert promise (pool_done p) (post_quicksort a r._2 hi pivot rb n s3 p fff ());
      //fold (pre_quicksort a lo r._1 lb pivot n s1);
      //assert promise 
      assert pool_alive fff p;// ** pool_alive fff p;
      return_promise (pool_done p) (pool_alive fff p);

      fold (post_quicksort a r._1 r._2 pivot pivot n s2 p fff ());
      assert promise (pool_done p) (post_quicksort a lo r._1 lb pivot n s1 p ff ())
       ** post_quicksort a r._1 r._2 pivot pivot n s2 p fff ()
       ** promise (pool_done p) (post_quicksort a r._2 hi pivot rb n s3 p fff ());

      return_promise (pool_done p) (post_quicksort a r._1 r._2 pivot pivot n s2 p fff ());

      combine_promises_posts a r._1 r._2 hi pivot pivot rb n #s2 #s3 p fff fff;
      combine_promises_posts a lo r._1 hi lb pivot rb n #s1 #(Seq.append s2 s3) p ff (sum_perm fff fff);

      //combine_promises_posts a lo r._1 r._2 lb pivot pivot n #s1 #s2 p ff fff;
      //combine_promises_posts a lo r._2 hi lb pivot rb n #(Seq.append s1 s2) #s3 p (sum_perm ff fff) fff;
      //combine_promises_posts a lo r._2 hi lb pivot rb n #(Seq.append s1 s2) #s3 p (sum_perm ff fff) fff;

      //assert (pure (sum_perm ff fff == f));
      //assert (pure (sum_perm (sum_perm ff fff) fff == sum_perm ff (sum_perm fff fff)));
      //assert (pure (sum_perm fff fff) == sum_perm ff (sum_perm fff fff)));
      assert (pure (sum_perm fff fff == ff));
      assert (pure (sum_perm ff ff == f));
      //assert (pure (sum_perm ff fff == f));
      //assert (pure (sum_perm ff (sum_perm fff fff) == f));

      rewrite (promise (pool_done p)
        (post_quicksort a lo hi lb rb n (Seq.append s1 (Seq.append s2 s3)) p (sum_perm (sum_perm ff fff) fff) ()))
        as (promise (pool_done p)
        (post_quicksort a lo hi lb rb n (Seq.append s1 (Seq.append s2 s3)) p f ()));

      assert (promise (pool_done p)
        (post_quicksort a lo hi lb rb n (Seq.append s1 (Seq.append s2 s3)) p f ()));
      
      //assert (Seq.append (Seq.append s1 s2) s3 == s0);
      assert (pure (permutation s0 (Seq.append s1 (Seq.append s2 s3))));
      //Seq.append_assoc s1 s2 s3;
      //assert (pure (Seq.append s1 (Seq.append s2 s3) == Seq.append (Seq.append s1 s2) s3));
      //assert (pure (Seq.append (Seq.append s1 s2) s3 == Seq.append s1 (Seq.append s2 s3)));
      //assert (pure (permutation s0 (Seq.append (Seq.append s1 s2) s3)));
        
      //rename (sum_perm (sum_perm ff fff) fff) to f;

       //** promise (pool_done p) (post_quicksort a r._2 hi pivot rb n s3 p fff ());


(*
      parallel
      requires (pts_to_range a lo r._1 full_perm s1 ** pure (pure_pre_quicksort a lo r._1 lb pivot n s1))
          and (pts_to_range a r._2 hi full_perm s3 ** pure (pure_pre_quicksort a r._2 hi pivot rb n s3))
      ensures (exists s. (pts_to_range a lo r._1 full_perm s ** pure (pure_post_quicksort a lo r._1 lb pivot n s1 s)))
          and (exists s. (pts_to_range a r._2 hi full_perm s ** pure (pure_post_quicksort a r._2 hi pivot rb n s3 s)))
      {
        // termination check
        assert_prop (hi - lo > (r._1 - 1) + 1 - lo);
        quicksort' a lo r._1 lb pivot n;// (Ghost.hide s1);
      }
      {
        // termination check
        assert_prop (hi - lo > hi - r._2);
        quicksort' a r._2 hi pivot rb n;
      };
      *)

      //with s1'. assert (pts_to_range a lo r._1 full_perm s1');
      //with s3'. assert (pts_to_range a r._2 hi full_perm s3');
      //join a lo r._1 r._2;
      //join a lo r._2 hi;
      //Seq.append_assoc s1' s2 s3';
      //append_permutations_3 s1 s2 s3 s1' s3';
      //with s. assert (pts_to_range a lo hi full_perm s);

      //assert (pure (hi - 1 < n /\ Seq.length s0 = hi - lo /\ Seq.length s = hi - lo /\ SZ.fits n /\ A.length a = n));
      //assert (pure (sorted s));
      //assert (pure (between_bounds s lb rb));
      //assert (pure (permutation s0 s));


      admit() // should work...
    }
    else // sequential
    {
      (*
      // termination check
      assert_prop (hi - lo > (r._1 - 1) + 1 - lo);
      quicksort' a lo r._1 lb pivot n;

      // termination check
      assert_prop (hi - lo > hi - r._2);
      quicksort' a r._2 hi pivot rb n;
  
      with s1'. assert (pts_to_range a lo r._1 full_perm s1');
      with s3'. assert (pts_to_range a r._2 hi full_perm s3');
      join a lo r._1 r._2;
      join a lo r._2 hi;
      Seq.append_assoc s1' s2 s3';
      append_permutations_3 s1 s2 s3 s1' s3';
      *)
      admit() // works
    }
  }
  else {
    admit() // works
  }
}
```
#pop-options
