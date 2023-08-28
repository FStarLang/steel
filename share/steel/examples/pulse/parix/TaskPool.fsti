module TaskPool

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open Promises
module T = FStar.Tactics

val pool : Type0
val pool_alive : (#[T.exact (`full_perm)]p : perm) -> pool -> vprop
val pool_done : pool -> vprop

val setup_pool (n:nat)
  : stt pool emp (fun p -> pool_alive #full_perm p)

val task_handle : pool -> a:Type0 -> (a -> vprop) -> Type0
val joinable : #p:pool -> #a:Type0 -> #post:_ -> th:(task_handle p a post) -> vprop
val joined   : #p:pool -> #a:Type0 -> #post:_ -> th:(task_handle p a post) -> vprop

val handle_solved
  (#p : pool) 
  (#a : Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : vprop

(* NOTE! Spawn only requires an *epsilon* of permission over the pool.
We do not have to be exclusive owners of it in order to queue a job,
even if that modifies it. How to model this under the hood? *)
val spawn
  (#a : Type0)
  (#pre : vprop) (#post : a -> vprop)
  (p:pool)
  ($f : unit -> stt a pre (fun (x:a) -> post x))
  : stt (task_handle p a post)
        ((exists_ (fun e -> pool_alive #e p)) ** pre)
        (fun th -> pool_alive p ** joinable th ** promise (joined th) (handle_solved th))

(* Spawn of a unit-returning task with no intention to join, simpler. *)
val spawn_
  (#pre #post : _)
  (p:pool) (f : unit -> stt unit pre (fun _ -> post))
  : stt unit ((exists_ (fun e -> pool_alive #e p)) ** pre)
             (fun prom -> pool_alive p ** promise (pool_done p) post)

(* If the pool is done, all pending joinable threads must be done *)
val must_be_done
  (#p : pool)
  (#a: Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt_ghost unit emp_inames (pool_done p ** joinable th) (fun () -> pool_done p ** handle_solved th)

val join0
  (#p:pool)
  (#a:Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt unit (joinable th) (fun () -> handle_solved th)

val extract
  (#p:pool)
  (#a:Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt a (handle_solved th) (fun x -> post x)
  
val join
  (#p:pool)
  (#a:Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt a (joinable th) (fun x -> post x)
// let join =
//   bind_stt (join0 th) (fun () ->
//   extract th)

(* We must exclusively own the pool in order to terminate it. *)
val teardown_pool
  (p:pool)
  : stt unit (pool_alive #full_perm p) (fun _ -> pool_done p)
