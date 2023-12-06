module Pulse.Lib.Mutex

open FStar.Ghost
open Steel.FractionalPermission

open Pulse.Lib.Pervasives

val mutex (#a:Type0) (p:a -> vprop) : Type0

val create (#a:Type0) (p:a -> vprop) (x:a)
  : stt (mutex p)
        (requires p x)
        (ensures fun _ -> emp)

val with_lock (#a:Type0) (#p:a -> vprop)
  (m:mutex p)
  (#b:Type)
  (#q:b -> vprop)
  (f:(r:ref a -> stt b (exists_ (fun (x:a) -> pts_to r x ** p x))
                       (fun (y:b) -> q y ** exists_ (fun (x:a) -> pts_to r x ** p x))))
  : stt b emp (fun r -> q r)
