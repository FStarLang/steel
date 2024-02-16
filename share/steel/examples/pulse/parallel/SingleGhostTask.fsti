module SingleGhostTasks

open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference


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

type extended_task (a: Type0): Type0 =
    a & task_status & GR.ref bool & GR.ref bool & GR.ref bool
    (* task, status, b_pre, b_post b_claimed *)

val task_res #a (t: extended_task a): vprop

val from_todo_to_ongoing #a #pre (t: extended_task a{t._2 == Todo}) (i: inv (guarded_inv t._3 pre)):
stt_atomic unit #Unobservable (singleton i)
(task_res t)
(fun () -> task_res (t._1, Ongoing, t._3, t._4, t._5) ** pre)

val from_ongoing_to_done #a #post (t: extended_task a{t._2 == Ongoing}) (i: inv (guarded_inv t._4 post)):
stt_atomic unit #Unobservable (singleton i)
(task_res t ** post)
(fun () -> task_res (t._1, Done, t._3, t._4, t._5))

val claim_post (#a: Type0) (#post: vprop) (t: extended_task a{t._2 == Done}) (i: inv (guarded_inv t._4 post)):
stt_atomic unit #Unobservable (singleton i)
(task_res t ** GR.pts_to t._5 #one_half false)
(fun () -> task_res t ** post ** GR.pts_to t._5 #one_half true)


(* Monotonic lists of extended tasks *)

type mono_list (a: Type) = list (extended_task a)