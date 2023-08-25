module Pulse.Lib.Invariants

open Pulse.Lib.Core

val inv (p:vprop) : Type

(* Does this have to be decidable? *)
val mem_inv (#p:vprop) : inames -> inv p -> Ghost.erased bool

val add_inv (#p:vprop) : inames -> inv p -> inames

// THIS SHOULD BE stt_unobservable

val new_invariant (p:vprop)
  : stt_ghost (inv p) emp_inames p (fun _ -> emp)
  
val with_invariant
  (#p:vprop)
  (#a : Type)
  (#pre : vprop)
  (#post : a -> vprop)
  (#opened : inames)
  (i : inv p{not (mem_inv opened i)})
  (f : unit -> stt_ghost a opened (p ** pre) (fun x -> p ** post x))
  : stt_ghost a (add_inv opened i) pre post
