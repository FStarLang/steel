module SingleGhostTask

open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference
module S = FStar.Set

module Lock = Pulse.Lib.SpinLock

(* Guarded invariants *)

val guarded_inv (gb: GR.ref bool) (p: vprop): vprop

val allocate_empty_guarded_inv (p: vprop):
stt_atomic (gb: GR.ref bool & inv (guarded_inv gb p)) #Unobservable emp_inames
emp (fun r -> GR.pts_to r._1 #one_half false)

let singleton #p (i:inv p) = add_inv emp_inames i

val put_in_guarded_inv (#gb: GR.ref bool) (#p: vprop) (i: inv (guarded_inv gb p)):
stt_atomic unit #Unobservable (singleton i) 
(p ** GR.pts_to gb #one_half false)
(fun () -> GR.pts_to gb #one_half true)

val take_from_guarded_inv (#gb: GR.ref bool) (#p: vprop) (i: inv (guarded_inv gb p)):
stt_atomic unit #Unobservable (singleton i)
(GR.pts_to gb #one_half true)
(fun () -> GR.pts_to gb #one_half false ** p)


(* Tasks *)

type task_status = | Todo | Ongoing | Done

let thunk bpre bpost
  = unit -> stt unit
  (GR.pts_to bpre #one_half true ** GR.pts_to bpost #one_half false)
  (fun () -> GR.pts_to bpre #one_half false ** GR.pts_to bpost #one_half true)


let lock_task (bdone: ref bool): vprop =
  exists* v f. pts_to bdone #f v ** pure (if not v then f == one_half else true)

type task =
    (bpre: GR.ref bool & bpost: GR.ref bool & thunk bpre bpost & (bdone: ref bool & Lock.lock (lock_task bdone)) & bclaimed: GR.ref bool)

val create_task (#pre #post: vprop) (f: (unit -> stt unit pre (fun () -> post))):
    stt (t: task & inv (guarded_inv t._2 post))
    pre
    (fun r -> GR.pts_to r._1._1 #one_half true ** GR.pts_to r._1._2 #one_half false ** pts_to r._1._4._1 #one_half false ** GR.pts_to r._1._5 false)

type extended_task: Type =
    task & task_status
    (* task, status, b_pre, b_post b_claimed *)

let same_extended_tasks (t1 t2: extended_task) =
    t1._1 == t2._1

let is_Todo (t: extended_task): bool =
    t._2 = Todo

let ongoing_condition (t: task) =
    pts_to t._4._1 #one_half false ** GR.pts_to t._5 #one_half false

val task_res (t: extended_task): vprop

val get_task_res_todo (t: task):
stt_ghost unit
(GR.pts_to t._1 #one_half true ** GR.pts_to t._2 #one_half false ** pts_to t._4._1 #one_half false ** GR.pts_to t._5 #one_half false)
(fun () -> task_res (t, Todo))


(* Easy to prove *TODO*: We take it from q *)
val from_todo_to_ongoing (t: extended_task{t._2 == Todo}): //(i: inv (guarded_inv t._1._2 pre)):
stt_ghost unit
(task_res t)
(fun () -> task_res (t._1, Ongoing) ** GR.pts_to t._1._1 #one_half true ** GR.pts_to t._1._2 #one_half false ** ongoing_condition t._1)

let task_done (t: task): vprop =
    exists* f. pts_to t._4._1 #f true

(*
val prove_ongoing (t: extended_task):
stt_ghost unit (task_res t ** GR.pts_to t._1._1 #one_half false ** GR.pts_to t._1._2 #one_half true ** ongoing_condition t._1)
(fun () -> task_res t ** GR.pts_to t._1._1 #one_half false ** GR.pts_to t._1._2 #one_half true ** ongoing_condition t._1 ** pure (t._2 == Ongoing))
*)

val from_ongoing_to_done (t: extended_task):
stt_atomic unit emp_inames
(task_res t ** GR.pts_to t._1._1 #one_half false ** GR.pts_to t._1._2 #one_half true ** ongoing_condition t._1 ** (exists* v. pts_to t._1._4._1 #one_half v))
(fun () -> task_res (t._1, Done) ** pts_to t._1._4._1 #one_half true ** task_done t._1)

(* Easy to prove done: Either q = [] and c = 0, or we
just wait on it and change its status... *)
val claim_post (#post: vprop) (t: extended_task{t._2 == Done}) (i: inv (guarded_inv t._1._2 post)):
stt_atomic unit #Unobservable (singleton i)
(task_res t ** GR.pts_to t._1._5 #one_half false)
(fun () -> task_res t ** post ** GR.pts_to t._1._5 #one_half true)

val duplicate_task_done (t: task):
stt_ghost unit (task_done t) (fun () -> task_done t ** task_done t)

val claim_post_from_done (#post: vprop) (t: extended_task) (i: inv (guarded_inv t._1._2 post)):
stt_atomic unit #Unobservable (singleton i)
(task_res t ** GR.pts_to t._1._5 #one_half false ** task_done t._1)
(fun () -> task_res t ** post ** GR.pts_to t._1._5 #one_half true ** task_done t._1)

val get_free_task_done_single (t: task):
stt_ghost unit (task_res (t, Done)) (fun ()-> task_res (t, Done) ** task_done t)



(* Monotonic lists of extended tasks *)

type mono_list: Type0 = list extended_task

let rec tasks_res (l: mono_list): vprop =
    match l with
    | [] -> emp
    | t::q -> task_res t ** tasks_res q