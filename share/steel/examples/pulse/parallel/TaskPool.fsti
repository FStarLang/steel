module TaskPool

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open Pulse.Lib.Par.Pledge
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
  (#[T.exact (`full_perm)]e : perm)
  (p:pool)
  ($f : unit -> stt a pre (fun (x:a) -> post x))
  : stt (task_handle p a post)
        (pool_alive #e p ** pre)
        (fun th -> pool_alive #e p ** joinable th ** pledge emp_inames (joined th) (handle_solved th))

(* Spawn of a unit-returning task with no intention to join, simpler. *)
val spawn_
  (#[T.exact (`full_perm)]e : perm)
  (#pre #post : _)
  (p:pool) (f : unit -> stt unit pre (fun _ -> post))
  : stt unit (pool_alive #e p ** pre)
             (fun prom -> pool_alive #e p ** pledge emp_inames (pool_done p) post)

(* If the pool is done, all pending joinable threads must be done *)
```pulse
ghost val 
fn must_be_done
  (#p : pool)
  (#a: Type0)
  (#post : (a -> vprop))
  (th : task_handle p a post)
requires pool_done p ** joinable th
ensures  pool_done p ** handle_solved th
```

```pulse
val 
fn join0
  (#p:pool)
  (#a:Type0)
  (#post : (a -> vprop))
  (th : task_handle p a post)
requires joinable th
ensures  handle_solved th
```

```pulse
val 
fn extract
  (#p:pool)
  (#a:Type0)
  (#post : (a -> vprop))
  (th : task_handle p a post)
requires handle_solved th
returns  x:a
ensures  post x
```

```pulse
ghost val 
fn split_alive
  (p:pool)
  (e:perm)
requires pool_alive #e p
ensures  pool_alive #(half_perm e) p ** pool_alive #(half_perm e) p
```

```pulse
val 
fn join
  (#p:pool)
  (#a:Type0)
  (#post : (a -> vprop))
  (th : task_handle p a post)
requires joinable th
returns  x:a
ensures  post x
```

(* We must exclusively own the pool in order to terminate it. *)
```pulse
val
fn teardown_pool
  (p:pool)
requires pool_alive #full_perm p
ensures  pool_done p
```

(* In other cases, however, some of the ownership may be in tasks within
the pool, so we require *some* permission plus a *promise* of the rest. *)
```pulse
val 
fn teardown_pool_partial
  (p:pool) (e:(e:perm{lesser_perm e full_perm}))
requires pool_alive #e p ** pledge_any (pool_done p) (pool_alive #(comp_perm e) p)
ensures  pool_done p
```