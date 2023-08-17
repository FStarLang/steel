module TaskPool

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open Promises

let pool : Type0 = magic()
let pool_alive : pool -> vprop = magic ()
let pool_done : pool -> vprop = magic ()

let setup_pool (n:nat)
  : stt pool emp (fun p -> pool_alive p)
  = magic ()

let task_handle : a:Type0 -> vprop -> Type0
  = magic ()

let spawn
  (#a : Type0)
  (#pre : vprop) (#post : vprop)
  (p:pool)
  ($f : unit -> stt a pre (fun (_:a) -> post))
  : stt (task_handle a post) (pool_alive p ** pre) (fun prom -> pool_alive p ** promise (pool_done p) post)
  = magic ()

let spawn_ #pre #post p f =
  bind_stt (spawn p f) (fun _ ->
  Pulse.Lib.Core.return () (fun _ -> pool_alive p ** promise (pool_done p) post))

let teardown_pool
  (p:pool)
  : stt unit (pool_alive p) (fun _ -> pool_done p)
  = magic ()
