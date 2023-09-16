module Domains

open Pulse.Lib.Pervasives
open Promises

val pool: Type u#2
val handler (p: pool) (a: Type0) (post: a -> vprop): Type

val pool_alive (f: perm) (p: pool): vprop
val pool_done (p: pool): vprop // duplicable
val active (#p: pool) (#a:Type0)
  (#post: a -> vprop) (h: handler p a post): vprop

val share_pool_alive (p: pool) (f1 f2: perm):
stt_ghost unit emp_inames
  (pool_alive (sum_perm f1 f2) p)
  (fun () -> pool_alive f1 p ** pool_alive f2 p)

val gather_pool_alive (p: pool) (f1 f2: perm):
stt_ghost unit emp_inames
  (pool_alive f1 p ** pool_alive f2 p)
  (fun () -> pool_alive (sum_perm f1 f2) p)



// number of threads
val create_pool (n: nat):
stt pool emp (fun p -> pool_alive full_perm p)

let stt_funct (a: Type0) pre post = (unit -> stt a pre post)

val spawn //(#a: Type0)
  (#pre: vprop) (#post: unit -> vprop)
  (p: pool)
  (funct: stt_funct unit pre post)
  (#f: perm)
: stt (handler p unit post)
(pool_alive f p ** pre)
(fun h -> pool_alive f p ** active h)

val join (#p: pool) (#a: Type0)
  (#post: a -> vprop) (h: handler p a post):
stt a (active h) post

(*
val get_promise (#p: pool)
  (#a: Type0) (#post: a -> vprop)
  (h: handler p a post)
: stt_ghost unit emp_inames (active h)
(fun () -> promise (pool_done p) (exists_ (fun v -> post v)))
*)
val get_promise (#p: pool)
  //(#a: Type0)
  (#post: unit -> vprop)
  (h: handler p unit post)
: stt_ghost unit emp_inames (active h)
(fun () -> promise (pool_done p) (post ()))

// maybe pool done is a bit too much for this?
val teardown_pool (p: pool) (f1: perm) (f2: perm{sum_perm f1 f2 == full_perm}):
stt unit
  (pool_alive f1 p ** promise (pool_done p) (pool_alive f2 p))
  (fun () -> pool_done p)