module Pulse.Extract.Main

open Pulse.Syntax.Base
open Pulse.Extract.CompilerLib
open Pulse.Syntax.Printer
open FStar.List.Tot

module L = FStar.List.Tot
module R = FStar.Reflection
module RT = FStar.Reflection.Typing
module T = FStar.Tactics.V2
module RB = Pulse.Readback
module Elab = Pulse.Elaborate.Pure
module E = Pulse.Typing.Env
module LN = Pulse.Syntax.Naming
module RU = Pulse.RuntimeUtils
module ECL = Pulse.Extract.CompilerLib

exception Extraction_failure of string

noeq
type env = { 
  uenv_inner: uenv;
  coreenv: Pulse.Typing.Env.env
}

let name = ppname & nat

let topenv_of_env (g:env) = E.fstar_env g.coreenv
let tcenv_of_env (g:env) = Pulse.Typing.elab_env g.coreenv
let uenv_of_env (g:env) = set_tcenv g.uenv_inner (tcenv_of_env g)
  
let debug (g:env) (f: unit -> T.Tac string)
  : T.Tac unit
  = if RU.debug_at_level (E.fstar_env g.coreenv) "pulse_extraction"
    then T.print (f())


let term_as_mlexpr (g:env) (t:term)
  : T.Tac mlexpr
  = let t = Elab.elab_term t in
    let uenv = uenv_of_env g in
    let t = normalize_for_extraction uenv t in
    let mlt, _, _ = term_as_mlexpr uenv t in
    mlt

let term_as_mlty (g:env) (t:term)
  : T.Tac mlty
  = let t = Elab.elab_term t in
    term_as_mlty (uenv_of_env g) t

let extend_env (g:env) (b:binder)
  : T.Tac (env & mlident & mlty & name)
  = let mlty = term_as_mlty g b.binder_ty in
    let x = E.fresh g.coreenv in
    let coreenv = E.push_binding g.coreenv x b.binder_ppname b.binder_ty in
    debug g (fun _ -> Printf.sprintf "Extending environment with %s : %s\n"
                                      (binder_to_string b)
                                      (term_to_string b.binder_ty));
    let uenv_inner, mlident = extend_bv g.uenv_inner b.binder_ppname x mlty in
    { uenv_inner; coreenv }, mlident, mlty, (b.binder_ppname, x)

let rec name_as_mlpath (x:T.name) 
  : T.Tac mlpath 
  = match x with
    | [] -> T.fail "Unexpected empty name"
    | [x] -> [], x
    | x :: xs ->
      let xs, x = name_as_mlpath xs in
      x :: xs, x

module R = FStar.Reflection.V2
let extract_constant (g:env) (c:T.vconst)
  : T.Tac mlconstant
  = let e = T.pack_ln (R.Tv_Const c) in
    let mle, _, _ = CompilerLib.term_as_mlexpr (uenv_of_env g) e in
    match mlconstant_of_mlexpr mle with
    | None -> T.raise (Extraction_failure "Failed to extract constant")
    | Some c -> c

let rec extend_env_pat_core (g:env) (p:pattern)
  : T.Tac (env & list mlpattern & list Pulse.Typing.Env.binding)
  = match p with
    | Pat_Dot_Term _ -> g, [], []
    | Pat_Var pp sort -> 
      let x = E.fresh g.coreenv in
      let pp = mk_ppname pp FStar.Range.range_0 in
      let ty = T.unseal sort in
      assume (not_tv_unknown ty);
      let ty = tm_fstar ty (T.range_of_term ty) in
      debug g (fun _ -> Printf.sprintf "Pushing pat_var %s : %s\n" (T.unseal pp.name) (term_to_string ty));
      let coreenv = E.push_binding g.coreenv x pp ty in
      let uenv_inner, mlident = extend_bv g.uenv_inner pp x mlty_top in
      { uenv_inner; coreenv },
      [ mlp_var mlident ],
      [ (x, tm_unknown) ]

    | Pat_Cons f pats ->
      let g, pats, bindings = 
        T.fold_left
          (fun (g, pats, bindings) (p, _) ->
            let g, pats', bindings' = extend_env_pat_core g p in
            g, pats @ pats', bindings@bindings')
          (g, [], [])
          pats
      in
      g, [mlp_constructor (name_as_mlpath f.fv_name) pats], bindings
    | Pat_Constant c ->
      let c = extract_constant g c in
      g, [mlp_const c], []
let extend_env_pat g p = 
  let g, pats, bs = extend_env_pat_core g p in
  match pats with
  | [p] -> g, p, bs
  | _ -> T.raise (Extraction_failure "Unexpected extraction of pattern")

let unit_val : term = tm_fstar Pulse.Reflection.Util.unit_tm Range.range_0
let is_erasable (p:st_term) : T.Tac bool = 
  let tag = T.unseal p.effect_tag in
  match tag with
  | Some STT_Ghost -> true
  | _ -> false
    
let head_and_args (t:term)
  : option (R.term & list R.argv) =
  match t.t with
  | Tm_FStar t0 -> Some (R.collect_app_ln t0)
  | _ -> None

let term_eq_string (s:string) (t:R.term) : bool =
  match R.inspect_ln t with
  | R.Tv_Const (R.C_String s') -> s=s'
  | _ -> false

let maybe_unfold_head (g:env) (f:R.term) 
  : option st_term
  = match R.inspect_ln f with
    | R.Tv_FVar f -> (
      let name = R.inspect_fv f in
      match R.lookup_typ (topenv_of_env g) name with
      | None -> None
      | Some se ->
        let attrs = R.sigelt_attrs se in
        if List.Tot.existsb (term_eq_string "inline") attrs
        then sigelt_extension_data se
        else None
    )
    | R.Tv_UInst f _ ->
      //No universe-polymorphic inlining ... yet
      None
    | _ -> None

let rec abs_body (n_args:nat) (t:st_term) =
  if n_args = 0 then Some t
  else (
    match t.term with 
    | Tm_Abs { body } -> abs_body (n_args - 1) body
    | _ -> None
  )


let maybe_inline (g:env) (head:term) (arg:term) : option st_term =
  match head_and_args head with
  | None -> None
  | Some (head, args) ->
    match maybe_unfold_head g head with
    | None -> None
    | Some body ->
      let args =
        L.map #R.argv (fun (t, _) -> assume (not_tv_unknown t); tm_fstar t Range.range_0) args
        @ [arg]
      in
      let n_args = L.length args in
      match abs_body n_args body with
      | None -> None
      | Some body ->
        let _, subst = 
          L.fold_right
            (fun arg (i, subst) ->
              i + 1,
              LN.DT i arg::subst)
            args
            (0, [])
        in
        Some (LN.subst_st_term body subst)

let rec extract (g:env) (p:st_term)
  : T.Tac (mlexpr & e_tag)
  = let erased_result = mle_unit, e_tag_erasable in
    debug g (fun _ -> Printf.sprintf "Extracting term@%s:\n%s\n" 
              (T.range_to_string p.range)
              (st_term_to_string p));
    if is_erasable p
    then erased_result
    else begin
      match p.term with
      | Tm_IntroPure _
      | Tm_ElimExists _
      | Tm_IntroExists _ 
      | Tm_Rewrite _ ->
        erased_result

      | Tm_Abs { b; q; body } -> 
        let g, mlident, mlty, name = extend_env g b in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract g body in
        let res = mle_fun [mlident, mlty] body in
        res, e_tag_pure

      | Tm_Return { term } ->
        term_as_mlexpr g term,
        e_tag_pure

      | Tm_STApp { head; arg } -> (
        match maybe_inline g head arg with
        | None ->
          let head = term_as_mlexpr g head in
          let arg = term_as_mlexpr g arg in
          mle_app head [arg], e_tag_impure
        | Some t -> extract g t
      )

      | Tm_Bind { binder; head; body } ->
        if is_erasable head
        then (
          let body = LN.subst_st_term body [LN.DT 0 unit_val] in
          debug g (fun _ -> Printf.sprintf "Erasing head of bind %s\nopened body to %s"
                              (st_term_to_string head)
                              (st_term_to_string body));
          extract g body
        )
        else (
          let head, _ = extract g head in
          let g, mlident, mlty, name = extend_env g binder in
          let body = LN.open_st_term_nv body name in
          let body, _ = extract g body in
          let mllb = mk_mllb mlident ([], mlty) head in 
          let mlletbinding = mk_mlletbinding false [mllb] in
          mle_let mlletbinding body, e_tag_impure
        )
    
      // tot here means non-stateful, head could also be ghost, we should rename it
      | Tm_TotBind { binder; head; body } ->
        let head = term_as_mlexpr g head in
        let g, mlident, mlty, name = extend_env g binder in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract g body in
        let mllb = mk_mllb mlident ([], mlty) head in 
        let mlletbinding = mk_mlletbinding false [mllb] in
        mle_let mlletbinding body, e_tag_impure
      
      | Tm_If { b; then_; else_ } ->
        let b = term_as_mlexpr g b in
        let then_, _ = extract g then_ in
        let else_, _ = extract g else_ in
        mle_if b then_ (Some else_), e_tag_impure

      | Tm_Match { sc; brs } ->
        let sc = term_as_mlexpr g sc in
        let extract_branch (pat0, body) =
          let g, pat, bs = extend_env_pat g pat0 in
          T.print (Printf.sprintf "Extracting branch with pattern %s\n"
                    (Pulse.Syntax.Printer.pattern_to_string pat0)
          //           // (String.concat ", " (L.map (fun (x, _) -> x) bs))
                    );
          let body = Pulse.Checker.Match.open_st_term_bs body bs in
          let body, _ = extract g body in
          pat, body
        in
        let brs = T.map extract_branch brs in
        mle_match sc brs, e_tag_impure

    
      | Tm_While { condition; body } ->
        let condition, _ = extract g condition in
        let body, _ = extract g body in
        let condition = mle_fun [("_", mlty_unit)] condition in
        let body = mle_fun [("_", mlty_unit)] body in
        let w = mle_app (mle_name (["Pulse"; "Lib"; "Core"], "while_")) [condition; body] in
        w, e_tag_impure

      | Tm_Par { body1; body2 } ->
        let body1, _ = extract g body1 in
        let body2, _ = extract g body2 in
        let body1 = mle_fun [("_", mlty_unit)] body1 in
        let body2 = mle_fun [("_", mlty_unit)] body2 in
        let p = mle_app (mle_name (["Pulse"; "Lib"; "Core"], "par")) [body1; body2] in
        p, e_tag_impure

      | Tm_WithLocal { binder; initializer; body } ->
        let initializer = term_as_mlexpr g initializer in
        let g, mlident, mlty, name = extend_env g { binder with binder_ty = binder.binder_ty } in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract g body in
        let allocator = mle_app (mle_name (["Pulse"; "Lib"; "Reference"] , "alloc")) [initializer] in
        let mllb = mk_mut_mllb mlident ([], mlty) allocator in
        let mlletbinding = mk_mlletbinding false [mllb] in
        mle_let mlletbinding body, e_tag_impure
      
      | Tm_WithLocalArray { binder; initializer; length; body } ->
        let initializer = term_as_mlexpr g initializer in
        let length = term_as_mlexpr g length in
        let g, mlident, mlty, name = extend_env g { binder with binder_ty = binder.binder_ty } in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract g body in
        //
        // Slice library doesn't have an alloc
        //
        // This is parsed by Pulse2Rust
        //
        let allocator = mle_app (mle_name (["Pulse"; "Lib"; "Array"; "Core"] , "alloc")) [initializer; length] in
        let mllb = mk_mut_mllb mlident ([], mlty) allocator in
        let mlletbinding = mk_mlletbinding false [mllb] in
        mle_let mlletbinding body, e_tag_impure

      | Tm_WithInv { body } ->
        extract g body
    
      | Tm_ProofHintWithBinders { t } -> T.fail "Unexpected constructor: ProofHintWithBinders should have been desugared away"
      | Tm_Admit _ -> T.raise (Extraction_failure (Printf.sprintf "Cannot extract code with admit: %s\n" (Pulse.Syntax.Printer.st_term_to_string p)))
    end

let rec generalize (g:env) (t:R.typ) (e:option st_term)
  : T.Tac (env &
           list mlident &
           R.typ &
           option st_term) =

  debug g (fun _ -> Printf.sprintf "Generalizing arrow:\n%s\n" (T.term_to_string t));
  let tv = R.inspect_ln t in
  match tv with
  | R.Tv_Arrow b c ->
    let {sort; ppname} = R.inspect_binder b in
    if R.Tv_Unknown? (R.inspect_ln sort)
    then T.raise (Extraction_failure "Unexpected unknown sort when generalizing")
    else if is_type g.uenv_inner sort
    then let cview = R.inspect_comp c in
         match cview with
         | R.C_Total t ->
           let x = Pulse.Typing.fresh g.coreenv in
           let xt = R.(pack_ln (Tv_Var (pack_namedv {uniq = x; sort = RT.sort_default; ppname}))) in
           let t = R.subst_term [R.DT 0 xt] t in
           let e =
             match e with
             | Some ({term = Tm_Abs {b; body}}) ->
               Some (LN.subst_st_term body [LN.DT 0 (tm_fstar xt Range.range_0)])
             | _ -> e in
           let namedv = R.pack_namedv {
            uniq = x;
            sort = FStar.Sealed.seal sort;
            ppname
           } in
           let uenv = extend_ty g.uenv_inner namedv in
           let coreenv =
             E.push_binding
               g.coreenv
               x
               (mk_ppname ppname FStar.Range.range_0)
               (tm_fstar sort FStar.Range.range_0) in
           let g = { g with uenv_inner = uenv; coreenv } in
           let g, tys, t, e = generalize g t e in
           g, (lookup_ty g.uenv_inner namedv)::tys, t, e
         | _ -> T.raise (Extraction_failure "Unexpected effectful arrow")
    else g, [], t, e
  
  | _ -> g, [], t, e

let debug_ = debug
  
let extract_pulse (g:uenv) (selt:R.sigelt) (p:st_term)
  : T.Tac (either mlmodule string) =
  
  let g = { uenv_inner=g; coreenv=initial_core_env g } in
  debug g (fun _ -> Printf.sprintf "About to extract:\n%s\n" (st_term_to_string p));
  let open T in
  try
    let sigelt_view = R.inspect_sigelt selt in
    match sigelt_view with
    | R.Sg_Let is_rec lbs ->
      if is_rec || List.length lbs <> 1
      then T.raise (Extraction_failure "Extraction of recursive lets is not yet supported")
      else
        let {lb_fv; lb_typ} = R.inspect_lb (List.Tot.hd lbs) in
        let g, tys, lb_typ, p = generalize g lb_typ (Some p) in
        let mlty = ECL.term_as_mlty g.uenv_inner lb_typ in
        if None? p
        then T.raise (Extraction_failure "Unexpected p");
        let tm, tag = extract g (Some?.v p) in
        debug_ g (fun _ -> Printf.sprintf "Extracted term: %s\n" (mlexpr_to_string tm));
        let fv_name = R.inspect_fv lb_fv in
        if List.Tot.length fv_name = 0
        then T.raise (Extraction_failure "Unexpected empty name");
        let mllb = mk_mllb (FStar.List.Tot.last fv_name) (tys, mlty) tm in
        Inl [mlm_let false [mllb]]
    | _ -> T.raise (Extraction_failure "Unexpected sigelt")
  with
  | Extraction_failure msg -> 
    Inr msg
  | e ->
    Inr (Printf.sprintf "Unexpected extraction error: %s" (RU.print_exn e))

let extract_pulse_sig (g:uenv) (selt:R.sigelt) (p:st_term)
  : T.Tac (either (uenv & iface) string) =

  let open T in
  try
    let sigelt_view = R.inspect_sigelt selt in
    match sigelt_view with
    | R.Sg_Let is_rec lbs ->
      if is_rec || List.length lbs <> 1
      then T.raise (Extraction_failure "Extraction of iface for recursive lets is not yet supported")
      else
        let {lb_fv; lb_typ} = R.inspect_lb (List.Tot.hd lbs) in
        let g0 = g in
        let g = { uenv_inner=g; coreenv=initial_core_env g } in
        let g, tys, lb_typ, _ = generalize g lb_typ None in
        debug_ g (fun _ -> Printf.sprintf "Extracting ml typ: %s\n" (T.term_to_string lb_typ));
        let mlty = ECL.term_as_mlty g.uenv_inner lb_typ in
        let g, _, e_bnd = extend_fv g0 lb_fv (tys, mlty) in
        Inl (g, iface_of_bindings [lb_fv, e_bnd])
    | _ -> T.raise (Extraction_failure "Unexpected sigelt")    
  with
  | Extraction_failure msg ->  Inr msg
  | e ->
    Inr (Printf.sprintf "Unexpected extraction error (iface): %s" (RU.print_exn e))
