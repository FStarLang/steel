module GhostTaskQueue

module L = FStar.List.Tot.Base
module P = FStar.Preorder

type task_status = | Todo | Ongoing | Done
type task_with_status (a: Type) = a & task_status
type mono_list (a: Type) = list (task_with_status a)
//val mono_list (a: Type): Type

open Pulse.Lib.Pervasives

module Lock = Pulse.Lib.SpinLock

let one_quart = half_perm (half_perm full_perm)

let own_res (#a: Type0) (r: ref (option a)) = (exists_ (fun v -> pts_to r #one_quart v))

let three_quart = sum_perm (half_perm full_perm) (half_perm (half_perm full_perm))

let own_None r = pts_to r #three_quart None
//let is_active (p: par_env): vprop = pts_to p._5._1._2 #three_quart None

//let current_task r = (t:task_elem & pos:nat & certificate r t pos)

let task_elem: Type u#1 = (
  a: Type0 // return type of the computation
  & r: ref (option a) // the reference where we put the result of the computation
  & Lock.lock (own_res r)//(exists_ (fun v -> pts_to r half v ** (if None? v then pts_to r half v else emp)))
  //& (unit_emp_stt_pure_pure a)
  // to create this thing
)

val ghost_mono_ref (a: Type u#1): Type0

val certificate (r:ghost_mono_ref task_elem) (t: task_elem) (pos: nat): Type0

val deadline (r: ghost_mono_ref task_elem): vprop

val duplicate_deadline (r: ghost_mono_ref task_elem):
stt_ghost unit emp_inames (deadline r) (fun () -> deadline r ** deadline r)

val small_inv (r: ghost_mono_ref task_elem) (q: list task_elem) (c: int): vprop 

val extract_deadline (r: ghost_mono_ref task_elem):
  stt_ghost unit emp_inames (small_inv r [] 0)
    (fun () -> small_inv r [] 0 ** deadline r)

let current_task r = (t:task_elem & pos:nat & certificate r t pos)
let is_active #r (ct: current_task r): vprop =
  (exists_ (fun v -> pts_to ct._1._2 #three_quart v))

// 1. enqueue task
val spawn_task_ghost
(r: ghost_mono_ref task_elem)
(q: list task_elem) (c: int) (t: task_elem)
(ct: current_task r)
: stt_ghost (erased (pos:nat & certificate r t pos)) emp_inames
(small_inv r q c ** pts_to t._2 #three_quart None ** is_active ct)
(fun _ -> small_inv r (t::q) c ** is_active ct)

// 2. pop task todo
val pop_task_ghost
(r: ghost_mono_ref task_elem)
(t: task_elem)
(q: list task_elem) (c: int)
(ct: current_task r)
: stt_ghost (erased (pos:nat & certificate r t pos)) emp_inames
(small_inv r (t::q) c ** is_active ct)
(fun _ -> small_inv r q (c + 1) ** pts_to t._2 #three_quart None ** is_active ct)

val prove_task_ongoing
  (#t: task_elem)
  (#pos: nat)
  (#v: option t._1)
  (r:ghost_mono_ref task_elem)
  (q: list task_elem) (c: int)
  (w:certificate r t pos)
: stt_ghost unit emp_inames
(small_inv r q c ** pts_to t._2 #three_quart v)
(fun () -> small_inv r q c ** pts_to t._2 #three_quart v ** pure (c > 0))

val prove_ongoing_non_neg
  (r:ghost_mono_ref task_elem)
  (q: list task_elem) (c: int)
: stt_ghost unit emp_inames
(small_inv r q c)
(fun () -> small_inv r q c ** pure (c >= 0))

let imp_vprop (b: bool) (p: vprop): vprop
  = if b then p else emp

// 3. conclude a task
val conclude_task_ghost
(#t: task_elem)
(#pos: nat)
(r: ghost_mono_ref task_elem)
(q: list task_elem) (c: int)
(x: t._1)
(w: certificate r t pos):
stt_ghost unit emp_inames
(small_inv r q c ** pts_to t._2 #three_quart (Some x))
(fun () -> small_inv r q (c - 1) ** imp_vprop (c = 1 && L.length q = 0) (deadline r))

val proof_promise (#t: task_elem) (#pos: nat)
  (r: ghost_mono_ref task_elem)
  (w:certificate r t pos)
: stt_ghost unit emp_inames
(deadline r)
(fun () -> deadline r ** (exists_ (fun f -> (exists_ (fun v ->
                          pts_to t._2 #f v ** pure (Some? v))))))