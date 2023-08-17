module Async

open Pulse.Lib.Pervasives

val asynch (a:Type0) (post : a -> vprop) : Type0

val async_joinable
  (#a : Type0)
  (post : a -> vprop)
  (h : asynch a post)
  : vprop

val async
  (#a : Type0)
  (#pre : vprop)
  (#post : (a -> vprop))
  (f : (unit -> stt a pre post))
  : stt (asynch a post) pre (fun h -> async_joinable post h)

val await
  (#a : Type0)
  (#post : (a -> vprop))
  (h : asynch a post)
  : stt a (async_joinable post h) (fun x -> post x)
