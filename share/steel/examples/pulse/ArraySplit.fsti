module ArraySplit

open Pulse.Lib.Core
open FStar.Ghost
module A = Pulse.Lib.Array

val pts_to_range
  (#elt: Type0) (a: A.array elt) (i:nat) (j:nat{i <= j})
  (s : Seq.seq elt{Seq.length s == j - i})
: Tot vprop

val array_range_intro
  (#elt: Type0) (a: A.array elt) (n : nat)
  (s : erased (Seq.seq elt){Seq.length s == n})
  : stt_ghost unit emp_inames
      (A.pts_to a s)
      (fun () -> pts_to_range a 0 n s)

val array_range_elim
  (#elt: Type0) (a: A.array elt) (n : nat)
  (s : erased (Seq.seq elt){Seq.length s == n})
  : stt_ghost unit emp_inames
      (pts_to_range a 0 n s)
      (fun () -> A.pts_to a s)

val array_split
  (#elt: Type0) (a: A.array elt)
  (lo:nat)
  (mid:nat{lo <= mid})
  (hi:nat{mid <= hi})
  (s : erased (Seq.lseq elt (hi-lo)))
  (_ : squash (lo <= mid /\ mid <= hi))
  : stt_ghost unit emp_inames
      (pts_to_range a lo hi s)
      (fun () -> pts_to_range a lo mid (Seq.slice s 0 (mid-lo)) 
              ** pts_to_range a mid hi (Seq.slice s (mid-lo) (hi-lo)))

val array_join
  (#elt: Type0) (a: A.array elt) (lo mid hi : nat)
  (s1: erased (Seq.seq elt){Seq.length s1 == mid - lo})
  (s2: erased (Seq.seq elt){Seq.length s2 == hi - mid})
  : stt_ghost unit emp_inames
      (pts_to_range a lo mid s1 ** pts_to_range a mid hi s2)
      (fun () -> pts_to_range a lo hi (Seq.append s1 s2))

val array_read
  (#elt: Type0) (a: A.array elt) (lo hi : nat) (idx:nat{lo <= idx /\ idx < hi})
  (s: erased (Seq.seq elt){Seq.length s == hi - lo})
  : stt elt
      (pts_to_range a lo hi s)
      (fun v -> pts_to_range a lo hi s ** pure (v == Seq.index s (idx-lo)))

val array_upd
  (#elt: Type0) (a: A.array elt) (lo hi : nat) (idx:nat{lo <= idx /\ idx < hi}) (v:elt)
  (s: erased (Seq.seq elt){Seq.length s == hi - lo})
  : stt unit
      (pts_to_range a lo hi s)
      (fun () -> pts_to_range a lo hi (Seq.upd s (idx-lo) v))
