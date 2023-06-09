module Pulse.Syntax.Builder
open Pulse.Syntax

let tm_return ctag insert_eq term = Tm_Return { ctag; insert_eq; term }
let tm_abs b q ascription body = Tm_Abs { b; q; ascription; body }
let tm_stapp head arg_qual arg = Tm_STApp { head; arg_qual; arg }
let tm_bind binder head body = Tm_Bind { binder; head; body }
let tm_totbind _binder head body = Tm_TotBind { head; body }
let tm_if b then_ else_ post = Tm_If { b; then_; else_; post }
let tm_elim_exists p = Tm_ElimExists { p }
let tm_intro_exists erased p witnesses = Tm_IntroExists { erased; p; witnesses; should_check=should_check_true }
let tm_while invariant condition condition_var body = Tm_While { invariant; condition; condition_var; body }
let tm_par pre1 body1 post1 pre2 body2 post2 = Tm_Par { pre1; body1; post1; pre2; body2; post2 }
let tm_with_local binder initializer body = Tm_WithLocal { binder; initializer; body }
let tm_rewrite t1 t2 = Tm_Rewrite { t1; t2 }
let tm_admit ctag u typ post = Tm_Admit { ctag; u; typ; post }
let tm_protect t = Tm_Protect { t }
let with_range t r = { term = t; range = r}
let tm_assert_with_binders bs v t = Tm_ProofHintWithBinders { hint_type=ASSERT; binders=bs; v; t }