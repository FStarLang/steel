module Pulse.Checker.Par

module T = FStar.Tactics.V2
module MT = Pulse.Typing.Metatheory

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common
open Pulse.Checker.Comp

open Pulse.Checker.ExtractFrame

#push-options "--z3rlimit 20 --print_full_names"
let check_par_compute_preconditions
  (allow_inst:bool)
  (g:env)
  //(t:st_term{Tm_Par? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (eL: st_term)
  (preL: vprop)
  (preR: vprop)
  (postL_hint:post_hint_opt g)
  (check':bool -> check_t)
  (modify_type_derivation: bool)
: 
T.Tac (t: st_term & c:comp{stateful_comp c /\ ~modify_type_derivation ==> comp_post_matches_hint c postL_hint} &
      frame:vprop & tot_typing g frame tm_vprop & st_typing g t c)
= (
  // this case cannot happen:
  // if Tm_Unknown? preL.t && not (Tm_Unknown? preR.t) then
  // 3 cases
    // 1. (_) and (_)
    // 2. (something) and (_)
    // 3. (something) and (something)
    // the fourth case (_) and (something) has been reduced to case 2
  if (Tm_Unknown? preL.t && Tm_Unknown? preR.t) then
      // case 1: (_) and (_)
      // we infer the left precondition, and use the inferred frame as the right precondition
      let (| eL, cL, preR, preR_typing, (eL_typing, _) |) = infer_frame_and_typecheck allow_inst eL pre_typing postL_hint check' modify_type_derivation in
      (| eL, cL, preR, preR_typing, eL_typing |)
    else 
    (
      // cases 2 and 3: (something) and (?)
      let (| preL, preL_typing |) = check_term_with_expected_type g preL tm_vprop in
      let (| eL, cL, eL_typing |) = check' allow_inst g eL preL (E preL_typing) postL_hint in
      let (| preR, preR_typing |): (frame:vprop & tot_typing g frame tm_vprop)
      = (
        if Tm_Unknown? preR.t then
          // case 2: (something) and (_)
          // we compute the right precondition as `context - left precondition`
          let (| preR, preR_typing, _ |) = remove_from_vprop preL pre_typing in
          (| preR, preR_typing |)
        else 
          // case 3: (something) and (something)
          // nothing to infer
          let (| preR, preR_typing |) = check_term_with_expected_type g preR tm_vprop in
          (| preR, E preR_typing |)
      ) in
      (| eL, cL, preR, preR_typing, eL_typing |)
  ))

let modify_type_derivation () = true

let check_par'
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
  let Tm_Par {pre1=preL; body1=eL; post1=postL; pre2=preR; body2=eR; post2=postR} = t.term in
  let postL_hint: post_hint_opt g = if Tm_Unknown? postL.t then None else Some (intro_post_hint g None postL) in
  let (| eL, cL, preR, preR_typing, eL_typing |):
    (t: st_term & c:comp &
      frame:vprop & tot_typing g frame tm_vprop & st_typing g t c)
  = check_par_compute_preconditions allow_inst g pre pre_typing eL preL preR postL_hint check' (modify_type_derivation ())
  // if modify type derivation is true, we basically ignore the postcondition provided by the user; not great
  in
   if C_ST? cL
    then
    (
      //T.print "LEFT PRE:";
      //T.print (term_to_string (comp_pre cL));
      //T.print "RIGHT PRE:";
      //T.print (term_to_string preR);
      let cL_typing = MT.st_typing_correctness eL_typing in
      let postR_hint = (if Tm_Unknown? postR.t then None else Some (intro_post_hint g None postR)) in
      let (| eR, cR, eR_typing |) = check' allow_inst g eR preR preR_typing postR_hint in
      if C_ST? cR && eq_univ (comp_u cL) (comp_u cR)
      then
        let cR_typing = MT.st_typing_correctness eR_typing in
        let x = fresh g in
        let d = T_Par _ _ _ _ _ x cL_typing cR_typing eL_typing eR_typing in
        repack (try_frame_pre pre_typing d) post_hint
      else fail g (Some eR.range) "par: cR is not stt")
    else fail g (Some eL.range) "par: cL is not stt"
    )
#pop-options

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
  let Tm_Par {pre1=preL; body1=eL; post1=postL; pre2=preR; body2=eR; post2=postR} = t.term in
  if Tm_Unknown? preL.t && not (Tm_Unknown? preR.t) then
    // swapping the two parallel branches
    let (t': st_term{Tm_Par? t'.term}) =
      { term = Tm_Par {pre1=preR; body1=eR; post1=postR; pre2=preL; body2=eL; post2=postL}; range = Range.range_0 } in
    check_par' allow_inst g t' pre pre_typing post_hint check'
  else
    check_par' allow_inst g t pre pre_typing post_hint check'
)