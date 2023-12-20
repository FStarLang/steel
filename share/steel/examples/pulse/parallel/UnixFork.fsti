module UnixFork

(* This module assumes an unstructured unix-style fork *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Par.Pledge

new
val thread : Type0

val joinable : thread -> vprop
val done     : thread -> vprop (* i.e. reapable/zombie *)

```pulse
val
fn fork 
  (#pre #post : vprop)
  (f : (unit -> stt unit pre (fun () -> post)))
requires pre
returns th : thread
ensures joinable th ** pledge emp_inames (done th) post
```

```pulse
val 
fn join
  (th : thread)
requires joinable th
ensures  done th
```
