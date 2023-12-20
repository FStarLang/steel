module Pulse.Main

module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
open FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker
open Pulse.Elaborate
open Pulse.Soundness
module Cfg = Pulse.Config
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer
module Rec = Pulse.Recursion

let debug_main g (s: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.main"
  then T.print (s ())
  else ()

let rec mk_abs (g:env) (qbs:list (option qualifier & binder & bv)) (body:st_term) (comp:comp)
: TacH st_term (fun _ -> not (Nil? qbs))
               (fun _ r -> match r with FStar.Tactics.Result.Success v _ -> Tm_Abs? v.term | _ -> False)
=
  let with_range (s:st_term') (r:range) : st_term =
    { term = s; range = r; effect_tag = default_effect_hint }
  in
  match qbs with
  | [(q, last, last_bv)] -> 
    let body = close_st_term body last_bv.bv_index in
    let comp = close_comp comp last_bv.bv_index in
    let asc = { annotated = Some comp; elaborated = None } in
    with_range (Pulse.Syntax.Builder.tm_abs last q asc body) body.range
  | (q, b, bv)::qbs ->
    let body = mk_abs g qbs body comp in
    let body = close_st_term body bv.bv_index in
    with_range (Pulse.Syntax.Builder.tm_abs b q empty_ascription body) body.range

let check_fndecl
    (d : decl{FnDefn? d.d})
    (g : Soundness.Common.stt_env{bindings g == []})
    (pre : term) (pre_typing : tot_typing g pre tm_vprop)
  : T.Tac (RT.dsl_tac_result_t (fstar_env g))
= 

  (* Maybe add a recursive knot before starting *)
  let FnDefn fn_d = d.d in
  let nm_orig = fst (inspect_ident fn_d.id) in // keep the original name
  let d =
    if fn_d.isrec
    then Recursion.add_knot g d.range d
    else d
  in

  let FnDefn { id; isrec; bs; comp; meas; body } = d.d in
  let nm_aux = fst (inspect_ident id) in

  if Nil? bs then
    fail g (Some d.range) "main: FnDefn does not have binders";
  let body = mk_abs g bs body comp in
  let rng = body.range in
  debug_main g (fun _ -> Printf.sprintf "\nbody after mk_abs:\n%s\n" (P.st_term_to_string body));

  let (| body, c, t_typing |) = Pulse.Checker.Abs.check_abs g body Pulse.Checker.check in

  Pulse.Checker.Prover.debug_prover g
    (fun _ -> Printf.sprintf "\ncheck call returned in main with:\n%s\nat type %s\n"
              (P.st_term_to_string body)
              (P.comp_to_string c));
  debug_main g
    (fun _ -> Printf.sprintf "\nchecker call returned in main with:\n%s\nderivation=%s\n"
              (P.st_term_to_string body)
              (Pulse.Typing.Printer.print_st_typing t_typing));

  let refl_t = elab_comp c in
  let refl_e = Pulse.RuntimeUtils.embed_st_term_for_extraction #st_term body (Some rng) in
  let blob = "pulse", refl_e in
  soundness_lemma g body c t_typing;
  let main_decl =
    let nm = fst (inspect_ident id) in
    if T.ext_getv "pulse:elab_derivation" <> ""
    then RT.mk_checked_let (fstar_env g) nm (elab_st_typing t_typing) refl_t
    else Pulse.Reflection.Util.mk_opaque_let (fstar_env g) nm (elab_st_typing t_typing) refl_t
  in
  (* Set the blob *)
  let main_decl =
    let (chk, se, _) = main_decl in
    let se = 
      if fn_d.isrec
      then (
        let nm = R.pack_ln (R.Tv_Const (R.C_String nm_orig)) in
        let attribute = `("pulse.recursive", `#(nm)) in
        let se = RU.add_attribute se (`(noextract_to "krml")) in
        let se = RU.add_noextract_qual se in
        let se : T.sigelt = RU.add_attribute se attribute in
        se
      )
      else se
    in
    (chk, se, Some blob)
  in
  let recursive_decls =
    if fn_d.isrec
    then Rec.tie_knot g rng nm_orig nm_aux d refl_t blob
    else []
  in
  main_decl :: recursive_decls

let main' (nm:string) (d:decl) (pre:term) (g:RT.fstar_top_env)
  : T.Tac (RT.dsl_tac_result_t g)
  = match Pulse.Soundness.Common.check_top_level_environment g with
    | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
    | Some g ->
      if RU.debug_at_level (fstar_env g) "Pulse" then 
        T.print (Printf.sprintf "About to check pulse decl:\n%s\n" (P.decl_to_string d));
      let (| pre, ty, pre_typing |) = Pulse.Checker.Pure.compute_tot_term_type g pre in
      if not (eq_tm ty tm_vprop) then
        fail g (Some pre.range) "pulse main: cannot typecheck pre at type vprop"; //fix range
      let pre_typing : tot_typing g pre tm_vprop = pre_typing in
      match d.d with
      | FnDefn _ ->
        check_fndecl d g pre pre_typing

let join_smt_goals () : Tac unit =
  let open FStar.Tactics.V2 in
  let open FStar.List.Tot in

  if RU.debug_at_level (top_env ()) "pulse.join" then
    dump "PULSE: Goals before join";

  (* Join *)
  let smt_goals = smt_goals () in
  set_goals (goals () @ smt_goals);
  set_smt_goals [];
  let n = List.Tot.length (goals ()) in
  ignore (repeat join);

  (* Heuristic rlimit setting :). Increase by 2 for every joined goal.
  Default rlimit is 5, so this is "saving" 3 rlimit units per joined
  goal. *)
  if not (Nil? (goals ())) then (
    let open FStar.Mul in
    let rlimit = get_rlimit() + (n-1)*2 in
    set_rlimit rlimit
  );

  if RU.debug_at_level (top_env ()) "pulse.join" then
    dump "PULSE: Goals after join";

  ()

let main nm t pre : RT.dsl_tac_t = fun g ->
  (* We use the SMT policy by default, to collect goals in the
  proofstate and discharge them all at the end, potentially joining
  them (see below). But it can be overriden to SMTSync by `--ext
  pulse:guard_policy=SMTSync`. *)
  if ext_getv "pulse:guard_policy" = "SMTSync" then
    set_guard_policy SMTSync
  else
    set_guard_policy SMT;

  let res = main' nm t pre g in

  if ext_getv "pulse:join" = "1"
     (* || ext_getv "pulse:join" <> "" *)
     // ^ Uncomment to make it true by default.
  then
    join_smt_goals();
  res

[@@plugin]
let check_pulse (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
                (nm:string)
  : RT.dsl_tac_t
  = fun env ->
      match PulseSyntaxExtension.ASTBuilder.parse_pulse env namespaces module_abbrevs content file_name line col with
      | Inl decl ->
        main nm decl tm_emp env

      | Inr None ->
        T.fail "Pulse parser failed"

      | Inr (Some (msg, range)) ->
        let i =
          Issue.mk_issue "Error"
                   (Printf.sprintf "%s: %s" (T.range_to_string range) msg)
                   (Some range)
                   None
                   []
        in
        T.log_issues [i];
        T.fail "Pulse parser failed"
