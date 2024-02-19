module GhostTaskQueue

module L = FStar.List.Tot.Base
module P = FStar.Preorder
module GR = Pulse.Lib.GhostReference

open SingleGhostTask

val is_mono_suffix: P.preorder mono_list

let rec task_in_queue (x: task) (pos:nat) (l: mono_list): prop =
  if pos + 1 = L.length l then (L.hd l)._1 == x
  else if pos + 1 < L.length l then task_in_queue x pos (L.tl l)
  else False

// 1. enqueue: when spawning a new task
// get a certificate for task_in_queue
let enqueue_todo (l: mono_list) (t: task) = (| (t, Todo)::l, L.length l |)

let rec count_ongoing (l: mono_list): nat =
match l with
| [] -> 0
| t::q -> (if t._2 = Ongoing then 1 else 0) + count_ongoing q

let get_actual_queue (l: mono_list): list task =
    L.map (fun (t: extended_task) -> t._1) (L.filter is_Todo l)

// 2. pop: when a worker starts working on a task
// it updates the task to "ongoing"
let rec pop_todo_task (l: mono_list{~(get_actual_queue l == [])})
: (t:task & r:mono_list{ get_actual_queue l == t::get_actual_queue r
                /\ count_ongoing r == count_ongoing l + 1 }
  & pos:nat{task_in_queue t pos r})
= match l with
| (t, Todo)::q -> (| t, (t, Ongoing)::q, L.length l - 1 |)
| t::q -> let (| x, q', pos |) = pop_todo_task q in (| x, t::q', pos |)

(** 3. concluding the task: when the worker is done **)
let rec close_task_bis (t: task) (pos: nat) (l: mono_list{task_in_queue t pos l /\ L.length l >= 1}): mono_list
= let (t', s)::q = l in
if pos + 1 = L.length l
  then (t', Done)::q // if s is not Ongoing, then we have too much permission
  else (t', s)::(close_task_bis t pos q)

(** ------------------------------------------------------
Part 2: Instantiation as a ghost monotonic reference
------------------------------------------------------ **)

module M = Pulse.Lib.GhostMonotonicHigherReference
open Pulse.Lib.Pervasives

//unfold
let ghost_mono_ref = M.ref mono_list is_mono_suffix

(** Part 3: Associated permissions: Reasoning done here **)

val certificate (r:ghost_mono_ref) (t: task) (pos: nat): Type0

let inv_ghost_queue (r: ghost_mono_ref): vprop =
  exists* l. M.pts_to r one_half l ** tasks_res l

val create_ghost_queue (_: unit):
stt_atomic (r: ghost_mono_ref & inv (inv_ghost_queue r)) #Unobservable emp_inames emp
(fun res -> M.pts_to res._1 one_half [])

val add_todo_task_to_queue
(r: ghost_mono_ref) (i: inv (inv_ghost_queue r)) (t: task) (l: mono_list):
stt_atomic (pos:nat & certificate r t pos) #Unobservable (singleton i)
(M.pts_to r one_half l ** GR.pts_to t._1 #one_half true ** GR.pts_to t._2 #one_half false ** pts_to t._4 #one_half false ** GR.pts_to t._5 #one_half false)
(fun _ -> M.pts_to r one_half (enqueue_todo l t)._1)

val pop_task_ghost (r: ghost_mono_ref) (i: inv (inv_ghost_queue r)) (l: mono_list{~(get_actual_queue l == [])}):
stt_atomic (pos:nat & certificate r (pop_todo_task l)._1 pos) #Unobservable (singleton i)
(M.pts_to r one_half l)
(fun _ -> M.pts_to r one_half (pop_todo_task l)._2 ** ongoing_condition (pop_todo_task l)._1 ** GR.pts_to (pop_todo_task l)._1._1 #one_half true ** GR.pts_to (pop_todo_task l)._1._2 #one_half false)

val conclude_task (t: task) (pos: nat) (r: ghost_mono_ref) (i: inv (inv_ghost_queue r)) (l: mono_list{task_in_queue t pos l}):
stt_atomic unit (singleton i)
(M.pts_to r one_half l ** GR.pts_to t._1 #one_half false ** GR.pts_to t._2 #one_half true ** ongoing_condition t ** (exists* v. pts_to t._4 #one_half v))
(fun () -> M.pts_to r one_half (close_task_bis t pos l) ** pts_to t._4 #one_half true ** task_done t)