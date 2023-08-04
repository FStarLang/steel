module Pulse.Typing.Util

open FStar.Tactics

(* Like T.check_equiv, but will make sure to not delay any VC. *)
val check_equiv_now : g:env -> t1:term -> t2:term -> Tac (option (equiv_token g t1 t2) & issues)
