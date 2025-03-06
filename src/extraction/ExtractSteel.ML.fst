module ExtractSteel.ML

open FStarC
open FStarC.Effect
open FStarC.Extraction.ML.Syntax
open FStarC.Syntax.Syntax
open FStarC.Extraction.ML.UEnv
open FStarC.Extraction.ML.Term

open FStarC.Class.Show
open FStarC.Syntax.Print {} // instances

module BU = FStarC.Util
module SS = FStarC.Syntax.Subst
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module Ident = FStarC.Ident

let dbg = Debug.get_toggle "steel_extraction"

let steel_memory_inv_lid = Ident.lid_of_str "Steel.Memory.inv"

let steel_new_invariant_lid = Ident.lid_of_str "Steel.Effect.Atomic.new_invariant"
let steel_st_new_invariant_lid = Ident.lid_of_str "Steel.ST.Util.new_invariant"

let steel_with_invariant_g_lid = Ident.lid_of_str "Steel.Effect.Atomic.with_invariant_g"
let steel_st_with_invariant_g_lid = Ident.lid_of_str "Steel.ST.Util.with_invariant_g"

let steel_with_invariant_lid = Ident.lid_of_str "Steel.Effect.Atomic.with_invariant"
let steel_st_with_invariant_lid = Ident.lid_of_str "Steel.ST.Util.with_invariant"

let hua (t:term) : option (S.fv & list S.universe & S.args) =
  let t = U.unmeta t in
  let hd, args = U.head_and_args_full t in
  let hd = U.unmeta hd in
  match (SS.compress hd).n with
  | Tm_fvar fv -> Some (fv, [], args)
  | Tm_uinst ({ n = Tm_fvar fv }, us) -> Some (fv, us, args)
  | _ -> None

let tr_expr (g:uenv) (t:term) : mlexpr & e_tag & mlty =
  let cb = FStarC.Extraction.ML.Term.term_as_mlexpr in
  let hua = hua t in
  if None? hua then
    raise NotSupportedByExtension;
  let Some (fv, us, args) = hua in
  if !dbg then
    BU.print1 "ExtractSteel.ML.tr_expr (%s)\n" (show hua);
  match fv, us, args with
  | fv, _, [_a; _fp; _fp'; _o; _p; _i; _body]
      when S.fv_eq_lid fv steel_with_invariant_g_lid
        || S.fv_eq_lid fv steel_st_with_invariant_g_lid ->
      ml_unit, E_PURE, MLTY_Erased

  | fv, _, [_a; _fp; _fp'; _o; _obs; _p; _i; (body, None)]
      when S.fv_eq_lid fv steel_with_invariant_lid
        || S.fv_eq_lid fv steel_st_with_invariant_lid ->
    let tm = S.mk_Tm_app body [as_arg unit_const] body.pos in
    cb g tm

  | fv, _, [_o; _p]
      when S.fv_eq_lid fv steel_new_invariant_lid
        || S.fv_eq_lid fv steel_st_new_invariant_lid ->
    ml_unit, E_PURE, ml_unit_ty

  | _ ->
    raise NotSupportedByExtension

let _ = register_pre_translate tr_expr
