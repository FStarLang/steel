module NewDomains

open Steel.Memory
open Steel.ST.Effect
open Steel.ST.Util
module Lock = Pulse.Lib.SpinLock
open Pulse.Lib.Pervasives
open Pulse.Lib.Core
module HR = Pulse.Lib.HigherReference
open FStar.List.Tot.Base
open GhostTaskQueue

type comp_task (t: task_elem) =
  unit -> stt t._1 (own_None t._2) (fun _ -> own_None t._2)

let task_queue: Type u#1 = list (t:task_elem & comp_task t)

let inv_task_queue
  (q: HR.ref task_queue) // the task queue
  (c: ref int) // a counter of how many tasks are currently being performed
  (r: ghost_mono_ref task_elem)
  : vprop
= (exists_ (fun vq ->
  exists_ (fun vc -> 
    HR.pts_to q vq ** pts_to c vc ** small_inv r (map dfst vq) vc **
    cond_deadline r (map dfst vq) vc
    )))

let par_env = (q: HR.ref task_queue & c: ref int & r: ghost_mono_ref task_elem & Lock.lock (inv_task_queue q c r))

val get_mono_list (p: par_env): ghost_mono_ref task_elem

let pure_handler a (p: par_env)
  = (res: ref (option a) & Lock.lock (own_res res)
  & t: erased task_elem & pos:erased nat & erased (certificate (get_mono_list p) t pos))

val spawn_emp
  (#a:Type0)
  (p: par_env)
  (ct: current_task p._3)
  (f: (par_env -> ct:erased (current_task p._3) -> unit -> stt a (is_active ct) (fun _ -> is_active ct)))
: stt (pure_handler a p) (is_active ct) (fun _ -> is_active ct)

val join_emp (#a:Type0) (p: par_env) (h: pure_handler a p)
: stt a emp (fun _ -> emp)

val worker (p: par_env): stt unit emp (fun () -> deadline (get_mono_list p))

(*
Parallel for loop

(parallel)
for i in ...
  invariant to_consume(i)
  invariant produced(i)
{
  // to_consume(i) ** produced(i)
  ghost_prep
  // to_consume(i+1) ** pre(i) ** produced(i)
  actual_task // might contain ghost code
  // to_consume(i+1) ** post(i) ** produced(i)
  ghost_post
  // to_consume(i+1) ** produced(i+1)
}

can be compiled into

for i in ...
  invariant to_consume(i)
         ** P(produced(i))
{
  // to_consume(i) ** P(produced(i))
  ghost_prep
  // to_consume(i+1) ** pre(i) ** P(produced(i))
  spawn_task(actual_task)
  // to_consume(i+1) ** P(post(i)) ** P(produced(i))
  bind_promise(post(i), produced(i))
  // to_consume(i+1) ** P(post(i) ** produced(i))
  modify_promise(ghost_post)
  // to_consume(i+1) ** P(produced(i+1))
}

redeem P(produced(n))

1. pre and post can be inferred using the extract_frame technique
2. the ghost prep and the ghost_post might be inferred
*)
