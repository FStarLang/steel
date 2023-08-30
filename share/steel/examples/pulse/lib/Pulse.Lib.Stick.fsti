module Pulse.Lib.Stick

open Pulse.Lib.Core

val stick : vprop -> vprop -> vprop

unfold
let ( @==> ) = stick

val elim_stick
  (#opens: _)
  (hyp concl: vprop)
: stt_ghost unit opens
    ((hyp @==> concl) ** hyp)
    (fun _ -> concl)

val intro_stick
  (#opens: _)
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: (
    (opens': inames) ->
    stt_ghost unit opens'
    (v ** hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit opens
    v
    (fun _ -> hyp @==> concl)
