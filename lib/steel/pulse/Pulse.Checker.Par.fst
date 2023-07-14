module Pulse.Checker.Par

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common
open Pulse.Checker.Comp
open Pulse.Syntax.Printer

module FV = Pulse.Typing.FV
module MT = Pulse.Typing.Metatheory

let print_term (t: term): T.Tac unit
  = T.print (term_to_string t)

let canon_comp (c:comp_st) : comp_st = 
  match readback_comp (elab_comp c) with
  | None -> c
  | Some (C_Tot _) -> c //should be impossible
  | Some c' ->
    c'

let canonicalize_st_typing (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
  : st_typing g t (canon_comp c)
  = let c' = canon_comp c in
    let x = fresh g in
    assume ( ~(x `Set.mem` freevars (comp_post c)) /\
            ~(x `Set.mem` freevars (comp_post c')) );
    assume (st_equiv_pre c c');
    let st_eq 
      : st_equiv g c c'
      = ST_VPropEquiv g c c' x (magic()) (magic()) (magic()) (magic()) (magic())
    in
    T_Equiv _ _ _ _ d st_eq



#push-options "--z3rlimit_factor 80"
let check_par
  (allow_inst:bool)
  (g:env)
  (t:st_term{Tm_Par? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check':bool -> check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  (
    let g = push_context "check_par" t.range g in
    let Tm_Par {pre1=preL; body1=eL; post1=postL;
                pre2=preR; body2=eR; post2=postR} = t.term in
    let (new_preL, new_preR): term & term =
  (
    if Tm_STApp? eL.term && Tm_Unknown? preL.t
    then let Tm_STApp { head; arg_qual=qual; arg } = eL.term in
    //let g = push_context "st_app" head.range g in        
    let (| head, ty_head, dhead |) = check_term g head in
    match is_arrow ty_head with
    | Some ({binder_ty=formal;binder_ppname=ppname}, bqual, comp_typ) ->
    (
      //assume false;
    if qual = bqual
    then
      let (| arg, darg |) = check_term_with_expected_type g arg formal in
      match comp_typ with
      | C_ST res
      | C_STAtomic _ res
      | C_STGhost _ res ->
        (let pre_app = comp_pre (open_comp_with comp_typ arg) in
        T.print (Printf.sprintf "Trying to frame in parallel block, context: %s and pre: %s\n"
                    (Pulse.Syntax.Printer.term_to_string pre)
                    (Pulse.Syntax.Printer.term_to_string (comp_pre (open_comp_with comp_typ arg))));
        match Pulse.Checker.Framing.check_frameable pre_typing pre_app with
        | Inr failure -> (preL, preR)
        | Inl frame_t -> (
          let f = frame_t._1 in
          //T.print (term_to_string f);
          (pre_app, f)
        )
      )
      | C_Tot _ -> (preL, preR)
    else (preL, preR)
    )
    | _ -> (preL, preR)
    else (preL, preR)
  ) in
  let (| preL, preL_typing |) =
    check_term_with_expected_type g new_preL tm_vprop in
  let postL_hint = (if Tm_Unknown? postL.t then None else Some (intro_post_hint g None postL)) in
  let (| eL, cL, eL_typing |) =
    check' allow_inst g eL preL (E preL_typing) postL_hint in
  (
  let (| preR, preR_typing |) =
    check_term_with_expected_type g new_preR tm_vprop in
  if C_ST? cL
  then
    let cL_typing = MT.st_typing_correctness eL_typing in
    let postR_hint = (if Tm_Unknown? postR.t then None else Some (intro_post_hint g None postR)) in
    let (| eR, cR, eR_typing |) =
      check' allow_inst g eR preR (E preR_typing) postR_hint in

    if C_ST? cR && eq_univ (comp_u cL) (comp_u cR)
    then
      let cR_typing = MT.st_typing_correctness eR_typing in
      let x = fresh g in
      let d = T_Par _ _ _ _ _ x cL_typing cR_typing eL_typing eR_typing in
      repack (try_frame_pre pre_typing d) post_hint
    else fail g (Some eR.range) "par: cR is not stt"
  else fail g (Some eL.range) "par: cL is not stt"
  ))
#pop-options