module Async

open Pulse.Lib.Pervasives

val asynch (a:Type0) (post : a -> vprop) : Type0

val async_joinable
  (#a : Type0)
  (#post : a -> vprop)
  (h : asynch a post)
  : vprop

```pulse
val
fn async
  (#a : Type0) (#pre : vprop) (#post : (a -> vprop))
  (f : (unit -> stt a pre post))
requires pre
returns h : asynch a post
ensures async_joinable h
```

```pulse
val
fn await (#a : Type0) (#post : (a -> vprop))
  (h : asynch a post)
requires async_joinable h
returns x : a
ensures post x
```
