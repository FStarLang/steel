module TaskPool

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open Promises

val pool : Type0
val pool_alive : pool -> vprop
val pool_done : pool -> vprop

val setup_pool (n:nat)
  : stt pool emp (fun p -> pool_alive p)

val task_handle : a:Type0 -> vprop -> Type0

val spawn
  (#a : Type0)
  (#pre : vprop) (#post : vprop)
  (p:pool)
  ($f : unit -> stt a pre (fun (_:a) -> post))
  : stt (task_handle a post) (pool_alive p ** pre) (fun prom -> pool_alive p ** promise (pool_done p) post)

val spawn_
  (#pre #post : _)
  (p:pool) (f : unit -> stt unit pre (fun _ -> post))
  : stt unit (pool_alive p ** pre) (fun prom -> pool_alive p ** promise (pool_done p) post)

val teardown_pool
  (p:pool)
  : stt unit (pool_alive p) (fun _ -> pool_done p)
