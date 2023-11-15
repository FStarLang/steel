module Pulse.RuntimeUtils
open FStar.Tactics
module T = FStar.Tactics

type context = FStar.Sealed.Inhabited.sealed #(list (string & option range)) []
val extend_context (tag:string) (r:option range) (ctx:context) : context

val debug_at_level_no_module (s:string) : bool
val debug_at_level (g:env) (s:string) : bool
val print_exn (e:exn) : string
val bv_set_range (x:bv) (r:range) : b:bv{b==x}
val bv_range (x:bv) : range
val binder_set_range (x:binder) (r:range) : b:binder{b==x}
val binder_range (x:binder) : range
val range_of_term (t:T.term) : range
val set_range (t:T.term) (r:range) : t':T.term{t == t'}
val set_use_range (t:T.term) (r:range) : t':T.term{t == t'}
val error_code_uninstantiated_variable (_:unit) : int
val is_range_zero (r:range) : Dv bool
val union_ranges (r0 r1:range) : range
val unfold_def (g:env) (nm:string) (fully:list string) (t:T.term) : option T.term   
val env_set_range (g:env) (r:range) : g':env{g==g'}
val env_set_context (g:env) (ctx:context) : g':env{g==g'}
val embed_st_term_for_extraction (d:'a) (r:option range): T.term
val unembed_st_term_for_extraction (d:T.term) : 'a
module R = FStar.Reflection.V2
val debug_subst (s:list R.subst_elt) (t:T.term) (r1 r2:T.term): y:T.term{ y == r1 }
val deep_compress (t:T.term) : r:T.term { t == r }
(* ***WARNING*** *)
(* This function is natively implemented against the F* compiler libraries
   to transform terms to use unary applications.

   Unfortunately, F* type inference differs in how it handles unary vs n-ary
   applications, notably in typeclass inference with refinement types, 
   and also coercion insertion.

   Pulse programs, to date, seem to rely on this unary application behavior.
   So, before calling back to the F* typechecker in Pulse.Checker.Pure
   we call this function to put terms in unary form.

   Ideally, the F* typechecker should not be sensitive to the arity of application
   nodes. If and when that is fixed, we should remove this function *)
val deep_transform_to_unary_applications (t:T.term) : r:T.term { t == r }
val map_seal (s:FStar.Sealed.sealed 't) (f: 't -> 'u) : FStar.Sealed.sealed 'u
val float_one : FStar.Float.float
val lax_check_term_with_unknown_universes (g:env) (t:T.term) : option T.term
val whnf_lax (g:env) (t:T.term) : T.term
module RT = FStar.Reflection.Typing
module T = FStar.Tactics.V2
val norm_well_typed_term
      (#g:T.env)
      (#t:R.term)
      (#eff:T.tot_or_ghost)
      (#k:Ghost.erased R.term)
      (_:Ghost.erased (RT.typing g t (eff, Ghost.reveal k)))
      (_:list norm_step)
  : T.Tac (
      t':R.term &
      Ghost.erased (RT.typing g t' (eff, Ghost.reveal k)) &
      Ghost.erased (RT.related g t RT.R_Eq t')
    )
