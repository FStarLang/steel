module Pulse.Lib.Stick
    
open Pulse.Lib.Core
friend Pulse.Lib.Core
open Steel.ST.Util

[@@"__reduce__"; "__steel_reduce__"]
let stick = implies_

(* TODO: This interface is opened-invariants parametric. Could we make
it `emp_inames` everywhere? *)

(* Using this indirection as Steel tactic relies on 'star' instead of ** *)
val __elim_stick
  (#opens: _)
  (hyp concl: vprop)
: stt_ghost unit opens
    ((hyp @==> concl) `star` hyp)
    (fun _ -> concl)
let __elim_stick #opened hyp concl =
  fun _ -> elim_implies #(Set.complement opened) hyp concl

let elim_stick = __elim_stick

(* Using this indirection as Steel tactic relies on 'star' instead of ** *)
val __intro_stick
  (#opens: _)
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: (
    (opens': inames) ->
    stt_ghost unit opens'
    (v `star` hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit opens
    v
    (fun _ -> hyp @==> concl)

let __intro_stick #opens hyp concl v f_elim =
  fun _ -> intro_implies #(Set.complement opens) hyp concl v
               (fun opens' -> f_elim (Set.complement opens') ())

let intro_stick = __intro_stick
