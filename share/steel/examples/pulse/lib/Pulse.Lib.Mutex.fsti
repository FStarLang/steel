module Pulse.Lib.Mutex

open Pulse.Lib.Core
open Pulse.Lib.Pervasives

val mutex (#a:Type0) (p:a -> vprop) : Type0

val new_mutex (#a:Type0) (p:a -> vprop) (x:a)
  : stt (mutex p)
        (requires p x)
        (ensures fun _ -> emp)

val mutex_guard (a:Type0) : Type0
val mutex_guard_vp (#a:Type0) (p:a -> vprop) (m:mutex_guard a) : vprop

val is_guard_for_lock (#a:Type0) (#p:a -> vprop) (mg:mutex_guard a) (m:mutex p) : prop

val mutex_lock (#a:Type0) (#p:a -> vprop) (m:mutex p)
  : stt (mutex_guard a)
        (requires emp)
        (ensures fun mg -> mutex_guard_vp p mg ** pure (mg `is_guard_for_lock` m))

val mutex_guard_to_ref (#a:Type0) (mg:mutex_guard a) : ref a

val mg_vp_pts_to (#a:Type0) (p:a -> vprop) (mg:mutex_guard a)
  : stt_ghost unit emp_inames
      (requires mutex_guard_vp p mg)
      (ensures fun _ -> exists* v. pts_to (mutex_guard_to_ref mg) v ** p v)

val pts_to_mg_vp (#a:Type0) (p:a -> vprop) (mg:mutex_guard a)
  : stt_ghost unit emp_inames
      (requires exists* v. pts_to (mutex_guard_to_ref mg) v ** p v)
      (ensures fun _ -> mutex_guard_vp p mg)

val mutex_unlock (#a:Type0) (#p:a -> vprop) (m:mutex p) (mg:mutex_guard a)
  : stt unit
        (requires mutex_guard_vp p mg ** pure (mg `is_guard_for_lock` m))
        (ensures fun _ -> emp)
