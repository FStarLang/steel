module GhostTaskQueuePoolAlive

module L = FStar.List.Tot.Base
module P = FStar.Preorder
module GR = Pulse.Lib.GhostReference

type task_status = | Todo | Ongoing | Done
type task_with_status (a: Type) = a & task_status
type mono_list (a: Type) = list (task_with_status a)
//val mono_list (a: Type): Type

(*
let small_inv (r: ghost_mono_ref task_elem) (q: list task_elem) (c: int): vprop 
= exists_ (fun l -> pts_to_ghost_queue_half r l **
  tasks_res_own l one_half **
  pure (count_ongoing l = c /\ get_actual_queue l == q)
  ** (if c = 0 && L.length q = 0 then deadline r
  else pts_to_ghost_queue_half r l ** tasks_res_own l one_quart)
)
*)

open Pulse.Lib.Pervasives

module Lock = Pulse.Lib.SpinLock

let one_quart = half_perm (half_perm full_perm)

let own_res (#a: Type0) (r: ref (option a)) = (exists_ (fun v -> pts_to r #one_quart v))

let three_quart = sum_perm (half_perm full_perm) (half_perm (half_perm full_perm))

let own_None r = pts_to r #three_quart None

let task_elem: Type u#1 = (
  a: Type0 // return type of the computation
  & r: ref (option a) // the reference where we put the result of the computation
  & Lock.lock (own_res r)//(exists_ (fun v -> pts_to r half v ** (if None? v then pts_to r half v else emp)))
)


//val ghost_mono_ref (a: Type u#1): Type0
//let gmref = erased (ghost_mono_ref task_elem)

val pool: Type // implemented as a ghost mono ref and a ghost bool ref

val certificate (p:pool) (t: task_elem) (pos: nat): Type0
let secret_certificate (p: pool) (t: task_elem): Type0 = (pos: nat & certificate p t pos)

val deadline (p: pool): vprop // ghost bool ref, false

val duplicate_deadline (p: pool):
stt_ghost unit emp_inames (deadline p) (fun () -> deadline p ** deadline p)

val small_inv (p: pool) (q: list task_elem) (c: int): vprop 

val pool_alive (f: perm) (p: pool): vprop // f/2 permission to the ghost bool ref, true

// 0. init queue with task
val init_ghost_queue: stt_ghost pool emp_inames emp (fun p -> small_inv p [] 0)

// 1. enqueue task
val spawn_task_ghost
(p: pool)
(q: list task_elem) (c: int)
(t: task_elem)
(#f: perm)
: stt_ghost (secret_certificate p t) emp_inames
(small_inv p q c ** pts_to t._2 #three_quart None ** pool_alive f p)
(fun _ -> small_inv p (t::q) c ** pool_alive f p)

// 2. pop task todo
val pop_task_ghost
(p: pool)
(t: task_elem)
(q: list task_elem) (c: int)
: stt_ghost (secret_certificate p t) emp_inames
(small_inv p (t::q) c)
(fun _ -> small_inv p q (c + 1) ** pts_to t._2 #three_quart None)

(*
val prove_task_ongoing
  (#t: task_elem)
  (#pos: nat)
  (#v: option t._1)
  (r:gmref)
  (q: list task_elem) (c: int)
  (w:certificate r t pos)
: stt_ghost unit emp_inames
(small_inv r q c ** pts_to t._2 #three_quart v)
(fun () -> small_inv r q c ** pts_to t._2 #three_quart v ** pure (c > 0))

val prove_ongoing_non_neg
  (r: gmref)
  (q: list task_elem) (c: int)
: stt_ghost unit emp_inames
(small_inv r q c)
(fun () -> small_inv r q c ** pure (c >= 0))
*)

// 3. conclude a task
val conclude_task_ghost
(#t: task_elem)
(#pos: nat)
(p: pool)
(q: list task_elem) (c: int)
(x: t._1)
(w: secret_certificate p t):
stt_ghost unit emp_inames
(small_inv p q c ** pts_to t._2 #three_quart (Some x))
(fun () -> small_inv p q (c - 1)) //imp_vprop (c = 1 && L.length q = 0) (deadline r))

val proof_promise (#t: task_elem) (#pos: nat)
  (p: pool)
  (w:secret_certificate p t)
: stt_ghost unit emp_inames
(deadline p)
(fun () -> deadline p ** (exists_ (fun f -> (exists_ (fun v ->
                          pts_to t._2 #f v ** pure (Some? v))))))
