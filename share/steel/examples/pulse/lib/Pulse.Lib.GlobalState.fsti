module Pulse.Lib.GlobalState

open FStar.Ghost
open Steel.FractionalPermission

open Pulse.Lib.Pervasives

val global_state (a:Type0) : Type0

val mk (#a:Type0) (f:unit -> stt a emp (fun _ -> emp))
  : stt (global_state a) emp (fun _ -> emp)

val belongs_to (#a:Type0) (r:ref a) (g:global_state a) : prop

val get (#a:Type0) (g:global_state a)
  : stt (ref a) emp (fun r -> (exists_ (fun (x:a) -> pts_to r #(half_perm full_perm) x)) **
                              pure (r `belongs_to` g))

val put (#a:Type0) (#v:erased a) (g:global_state a) (r:ref a)
  : stt unit (pts_to r #(half_perm full_perm) v ** pure (r `belongs_to` g)) (fun _ -> emp)
