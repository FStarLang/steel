module Promises

open Pulse.Lib.Pervasives

val promise (f:vprop) (v:vprop) : vprop

(* Anything that holds now holds in the future too. *)
val return_promise (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames v (fun _ -> promise f v)

val make_promise (f:vprop) (v:vprop) (extra:vprop)
  ($k : unit -> stt_ghost unit emp_inames (f ** extra) (fun _ -> f ** v))
  : stt_ghost unit emp_inames extra (fun _ -> promise f v)

val redeem_promise (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames (f ** promise f v) (fun () -> f ** v)

val bind_promise (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop)
        (k : unit -> stt_ghost unit emp_inames (f ** extra ** v1) (fun () -> f ** promise f v2))
  : stt_ghost unit emp_inames (promise f v1 ** extra) (fun () -> promise f v2)

(* Weaker variant, the proof does not use f. It's implement
by framing k with f and then using the above combinator. Exposing
only in case it's useful for inference. *)
val bind_promise' (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop)
        (k : unit -> stt_ghost unit emp_inames (extra ** v1) (fun () -> promise f v2))
  : stt_ghost unit emp_inames (promise f v1 ** extra) (fun () -> promise f v2)

val join_promise (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (promise f v1 ** promise f v2)
              (fun () -> promise f (v1 ** v2))

val split_promise (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (promise f (v1 ** v2))
              (fun () -> promise f v1 ** promise f v2)

// TODO: write a variant that assumes f too
val rewrite_promise (#f:vprop) (v1 : vprop) (v2 : vprop)
  (k : unit -> stt_ghost unit emp_inames v1 (fun _ -> v2))
  : stt_ghost unit
              emp_inames
              (promise f v1)
              (fun _ -> promise f v2)
