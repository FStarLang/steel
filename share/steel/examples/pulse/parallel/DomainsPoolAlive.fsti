module DomainsPoolAlive

open Steel.Memory
open Steel.ST.Effect
open Steel.ST.Util
module Lock = Pulse.Lib.SpinLock
open Pulse.Lib.Pervasives
open Pulse.Lib.Core
module HR = Pulse.Lib.HigherReference
open FStar.List.Tot.Base

open GhostTaskQueuePoolAlive
open Promises

val par_env: Type
val certif (t:task_elem) (p: par_env): Type

//let par_env_alive (f: perm) (p: par_env) = pool_alive f p._3
val par_env_alive (f: perm) (p: par_env): vprop
val par_env_done (p: par_env): vprop

val pure_handler (a: Type) (p: par_env): Type
val get_ref_handler (#a: Type) (#p: par_env) (h: pure_handler a p): ref (option a)

let task_done #a #p (h: pure_handler a p): vprop
  = exists_ (fun f -> exists_ (fun v -> pts_to (get_ref_handler h) #f v ** pure (Some? v)))

val spawn_emp
  (#a:Type0)
  (p: par_env)
  (funct: (unit -> stt a emp (fun _ -> emp)))
  (f: perm)
: stt (pure_handler a p) (par_env_alive f p) (fun h -> par_env_alive f p ** promise (par_env_done p) (task_done h))

// TODO: Align with promise?
val join_emp (#a:Type0) (p: par_env) (h: pure_handler a p): stt a emp (fun _ -> emp)

val worker (p: par_env): stt unit emp (fun () -> par_env_done p)

val create_par_env (n: nat):
stt par_env emp (fun p -> par_env_alive full_perm p)

val kill_par_env (p: par_env):
stt unit (par_env_alive full_perm p) (fun () -> par_env_done p)

//  let pure_handler a (p: par_env)
//   = (res: ref (option a) & Lock.lock (own_res res)
//   & erased (t: task_elem{t._1 == a /\ t._2 == res} & (certif t p)))



//val pool_alive (f: perm) (r: ref bool): vprop

//type comp_task (t: task_elem) =
//  unit -> stt t._1 emp (fun _ -> emp)

//let task_queue: Type u#1 = list (t:task_elem & comp_task t)

(*
let inv_task_queue
  (q: HR.ref task_queue) // the task queue
  (c: ref int) // a counter of how many tasks are currently being performed
  (r: erased pool)
  : vprop
= (exists_ (fun vq ->
  exists_ (fun vc -> 
    HR.pts_to q vq ** pts_to c vc ** small_inv r (map dfst vq) vc
    //** cond_deadline r (map dfst vq) vc // TODO: Remove
    )))
    *)

//let par_env = (q: HR.ref task_queue & c: ref int & r: pool & Lock.lock (inv_task_queue q c r))
//let certif (t:task_elem) (p: par_env) = secret_certificate p._3 t