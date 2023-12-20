module MSort

open FStar.Ghost
open Pulse.Lib.Pervasives
open TaskPool
module A = Pulse.Lib.Array
open ArraySplit
module S = FStar.Seq


assume val sort : Seq.seq int -> Seq.seq int
assume val sorted : Seq.seq int -> bool
assume val sort_is_sorted (s:Seq.seq int) : Lemma (sorted (sort s))
assume val sort_len (s:Seq.seq int)
  : Lemma (S.length (sort s) == S.length s)
          [SMTPat (S.length (sort s))]
          
assume val singl_is_sorted (s : S.seq int)
  : Lemma (requires S.length s < 2)
          (ensures s == sort s)

assume val merge : Seq.seq int -> Seq.seq int -> Seq.seq int
assume val merge_len (s1 s2 : S.seq int)
  : Lemma (ensures S.length (merge s1 s2) == S.length s1 + S.length s2)
          [SMTPat (merge s1 s2)]
assume val merge_sorted' (s1 s2 : S.seq int)
  : Lemma (ensures merge (sort s1) (sort s2) == sort (s1 `S.append` s2))
          [SMTPat (merge (sort s1) (sort s2))]

assume val merge_sorted (s1 s2 : S.seq int)
  : Lemma (requires sorted s1 /\ sorted s2)
          (ensures sorted (merge s1 s2))
          [SMTPat (sorted (merge s1 s2))]
          
assume val append_slice #a (s : S.seq a)
  (l1:nat) (l2 : nat{S.length s == l2 /\ l1 <= l2})
  : Lemma (S.append (S.slice s 0 l1) (S.slice s l1 l2) == s)
          [SMTPat (S.append (S.slice s 0 l1) (S.slice s l1 l2))]

```pulse
fn
merge_impl
  (a : A.array int) (lo mid hi : nat) (_:squash (lo <= mid /\ mid <= hi))
  (s1 : erased (S.lseq int (mid-lo)))
  (s2 : erased (S.lseq int (hi-mid)))
  requires pts_to_range a lo mid s1 ** pts_to_range a mid hi s2
  ensures pts_to_range a lo hi (merge s1 s2)
{
  admit()
}
```

#set-options "--debug Sorting --debug_level SMTQuery"

// FIXME: using a recursive functions fails weirdly.
```pulse
fn
msort
  (a : A.array int)
  (cb : (
    (lo:nat) -> (hi : (hi:nat{lo <= hi})) ->
    (s : erased (s:Seq.seq int{S.length s == hi-lo})) ->
    stt unit (pts_to_range #int a lo hi s)
             (fun () -> pts_to_range a lo hi (sort s))
  ))
  (lo:nat) (hi : (hi:nat{lo <= hi}))
  (s : erased (S.lseq int (hi-lo)))
  requires pts_to_range a lo hi (reveal s)
  ensures  pts_to_range a lo hi (sort (reveal s))
{
  if (hi - lo < 2) {
    singl_is_sorted s;
    ()
  } else {
    let mid = (hi+lo) / 2;

    array_split a lo mid hi s ();

    with s1. assert (pts_to_range a lo mid s1);
    with s2. assert (pts_to_range a mid hi s2);

    cb lo mid s1;
    cb mid hi s2;

    merge_impl a lo mid hi () (sort s1) (sort s2);

    ()
  }
}
```
