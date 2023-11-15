module Pulse.Checker.If

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module Metatheory = Pulse.Typing.Metatheory

#set-options "--z3rlimit 40" // :-(

(* For now we just create a term with the union,
but this could potentially be smarter *)
let compute_iname_join (is1 is2 : term) : term =
  tm_join_inames is1 is2
  
let tm_sub_inv_ghost
   (g : env) (e : st_term) (c : st_comp)
   (is1 is2 : term)
   (d : st_typing g e (C_STGhost is1 c))
  : T.Tac (st_typing g e (C_STGhost is2 c))
  // TODO: check validity of is1 <: is2
  = 
    T_SubInvsGhost g e is1 is2 c (magic ()) d

let tm_sub_inv_atomic
   (g : env) (e : st_term) (c : st_comp)
   (is1 is2 : term)
   (d : st_typing g e (C_STAtomic is1 c))
  : T.Tac (st_typing g e (C_STAtomic is2 c))
  // TODO: check validity of is1 <: is2
  = T_SubInvsAtomic g e is1 is2 c (magic ()) d

effect TacS (a:Type) (pre : Type0) (post : (_:a{pre}) -> Type0) =
  Tactics.TacH a (requires (fun _ -> pre))
                 (ensures (fun _ r -> pre /\ (
                                      match r with
                                      | Tactics.Result.Success r _ -> post r
                                      | _ -> True))) // does not guarantee anything on failure

let lift_atomic_to_st
  (g : env)
  (e : st_term)
  (c : comp_st{C_STAtomic? c})
  (d : st_typing g e c)
  : Pure (c':comp_st & st_typing g e c')
         (requires True)
         (ensures fun (| c', _ |) ->
             st_comp_of_comp c' == st_comp_of_comp c /\
             ctag_of_comp_st c' == STT)
= let C_STAtomic _ c_st = c in
  let c' = C_ST c_st in
  let d' : st_typing g e c' =
    T_Lift g e c c' d (Lift_STAtomic_ST g c)
  in
  (| c', d' |)

let lift_ghost_to_atomic
  (g : env)
  (e : st_term)
  (c : comp_st{C_STGhost? c})
  (d : st_typing g e c)
  : TacS (c':comp_st & st_typing g e c')
         (requires True)
         (ensures fun (| c', _ |) ->
             st_comp_of_comp c' == st_comp_of_comp c /\
             ctag_of_comp_st c' == STT_Atomic /\
             C_STGhost?.inames c == C_STAtomic?.inames c')
= let C_STGhost inames c_st = c in
  let w = get_non_informative_witness g (comp_u c) (comp_res c) in
  let c' = C_STAtomic inames c_st in
  let d' : st_typing g e c' =
    T_Lift g e c c' d (Lift_STGhost_STAtomic g c w)
  in
  (| c', d' |)

(* This matches the effects of the two branches, without
necessarily matching inames. *)
let lift_if_branches
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  : TacS (c_then':comp_st &
          c_else':comp_st &
          st_typing g_then e_then c_then' &
          st_typing g_else e_else c_else')
         (requires comp_pre c_then == comp_pre c_else)
         (ensures fun (| c_then', c_else', _, _ |) ->
            st_comp_of_comp c_then' == st_comp_of_comp c_then /\
            st_comp_of_comp c_else' == st_comp_of_comp c_else /\
            ctag_of_comp_st c_then' == ctag_of_comp_st c_else')
= let g = g_then in
  match c_then, c_else with
  | C_STGhost _ _, C_STGhost _ _ 
  | C_STAtomic _ _, C_STAtomic _ _
  | C_ST _, C_ST _ ->
    (* Nothing to do *)
    (| c_then, c_else, e_then_typing, e_else_typing |)

  | C_STAtomic _ _ , C_ST _ ->
    let (| c_then', e_then_typing' |) = lift_atomic_to_st g_then e_then c_then e_then_typing in
    (| c_then', c_else, e_then_typing', e_else_typing |)

  | C_ST _, C_STAtomic _ _ ->
    let (| c_else', e_else_typing' |) = lift_atomic_to_st g_else e_else c_else e_else_typing in
    (| c_then, c_else', e_then_typing, e_else_typing' |)

  | C_STGhost _ _, C_STAtomic _ _ ->
    let (| c_then', e_then_typing' |) = lift_ghost_to_atomic g_then e_then c_then e_then_typing in
    (| c_then', c_else, e_then_typing', e_else_typing |)

  | C_STAtomic _ _, C_STGhost _ _ ->
    let (| c_else', e_else_typing' |) = lift_ghost_to_atomic g_else e_else c_else e_else_typing in
    (| c_then, c_else', e_then_typing, e_else_typing' |)

  | C_STGhost _ _, C_ST _ ->
    let (| c_then', e_then_typing' |) = lift_ghost_to_atomic g_then e_then c_then  e_then_typing  in
    let (| c_then', e_then_typing' |) = lift_atomic_to_st    g_then e_then c_then' e_then_typing' in
    (| c_then', c_else, e_then_typing', e_else_typing |)

  | C_ST _, C_STGhost _ _ ->
    let (| c_else', e_else_typing' |) = lift_ghost_to_atomic g_else e_else c_else  e_else_typing  in
    let (| c_else', e_else_typing' |) = lift_atomic_to_st    g_else e_else c_else' e_else_typing' in
    (| c_then, c_else', e_then_typing, e_else_typing' |)

let inames_of_comp (c:comp_st) : term =
  match c with
  | C_ST _ -> tm_emp_inames
  | C_STAtomic inames _ -> inames
  | C_STGhost inames _ -> inames

(* Takes the two branches, with already matched effect,
and matches their invariants (unless C_ST) *)
let match_inames
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  : TacS (c_then':comp_st &
          c_else':comp_st &
          st_typing g_then e_then c_then' &
          st_typing g_else e_else c_else')
         (requires ctag_of_comp_st c_then == ctag_of_comp_st c_else)
         (ensures fun (| c_then', c_else', _, _ |) ->
            st_comp_of_comp c_then' == st_comp_of_comp c_then /\
            st_comp_of_comp c_else' == st_comp_of_comp c_else /\
            ctag_of_comp_st c_then' == ctag_of_comp_st c_then /\
            ctag_of_comp_st c_else' == ctag_of_comp_st c_else /\
            inames_of_comp c_then' == inames_of_comp c_else'
         )
= match c_then, c_else with
  | C_ST _, C_ST _ ->
    (| c_then, c_else, e_then_typing, e_else_typing |)

  | C_STAtomic inames1 stc_then, C_STAtomic inames2 stc_else ->
    if eq_tm inames1 inames2 then
      (* easy case; an optimization *)
      (| c_then, c_else, e_then_typing, e_else_typing |)
    else (
      let is = compute_iname_join inames1 inames2 in
      let e_then_typing = tm_sub_inv_atomic g_then e_then stc_then inames1 is e_then_typing in
      let e_else_typing = tm_sub_inv_atomic g_else e_else stc_else inames2 is e_else_typing in
      (| C_STAtomic is stc_then, C_STAtomic is stc_else, e_then_typing, e_else_typing |)
    )

  | C_STGhost inames1 stc_then, C_STGhost inames2 stc_else ->
    if eq_tm inames1 inames2 then
      (* easy case; an optimization *)
      (| c_then, c_else, e_then_typing, e_else_typing |)
    else (
      let is = compute_iname_join inames1 inames2 in
      let e_then_typing = tm_sub_inv_ghost g_then e_then stc_then inames1 is e_then_typing in
      let e_else_typing = tm_sub_inv_ghost g_else e_else stc_else inames2 is e_else_typing in
      (| C_STGhost is stc_then, C_STGhost is stc_else, e_then_typing, e_else_typing |)
    )

let combine_if_branches
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  : TacS (c:comp_st &
          st_typing g_then e_then c &
          st_typing g_else e_else c)
         (requires comp_pre c_then == comp_pre c_else)
         (ensures fun (| c, _, _ |) -> st_comp_of_comp c == st_comp_of_comp c_then)
=
  let g = g_then in
  if not (eq_st_comp (st_comp_of_comp c_then) (st_comp_of_comp c_else)) then
    fail g None "Cannot combine then and else branches (different st_comp)";
  let (| c_then', c_else', e_then_typing', e_else_typing' |) =
    lift_if_branches g_then e_then c_then e_then_typing g_else e_else c_else e_else_typing in
  assert (ctag_of_comp_st c_then' == ctag_of_comp_st c_else');
  let (| c_then'', c_else'', e_then_typing'', e_else_typing'' |) =
    match_inames g_then e_then c_then' e_then_typing' g_else e_else c_else' e_else_typing' in
  assert (c_then'' == c_else'');
  (| c_then'', e_then_typing'', e_else_typing'' |)

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
let check
  (g:env)
  (pre:term)
  (pre_typing: tot_typing g pre tm_vprop)
  (post_hint:post_hint_for_env g)
  (res_ppname:ppname)
  (b:term)
  (e1 e2:st_term)
  (check:check_t)
  : T.Tac (checker_result_t g pre (Some post_hint)) =
  
  let g = Pulse.Typing.Env.push_context g "check_if" e1.range in

  let (| b, b_typing |) =
    check_tot_term_with_expected_type g b tm_bool in

  let post = post_hint.post in
  let hyp = fresh g in
  let g_with_eq (eq_v:term) =
    push_binding g hyp (mk_ppname_no_range "_if_hyp") (mk_eq2 u0 tm_bool b eq_v)
  in

  let check_branch (eq_v:term) (br:st_term) (is_then:bool)
    : T.Tac (br:st_term { ~(hyp `Set.mem` freevars_st br) } &
             c:comp_st { comp_pre c == pre /\ comp_post_matches_hint c (Some post_hint)} &
             st_typing (g_with_eq eq_v) br c) =
    let g_with_eq = g_with_eq eq_v in
    let pre_typing = 
      Metatheory.tot_typing_weakening_single
        pre_typing
        hyp 
        (mk_eq2 u0 tm_bool b eq_v)
    in
    
    let (| br, c, d |) =
      let ppname = mk_ppname_no_range "_if_br" in
      let r =
        check g_with_eq pre pre_typing (Some post_hint) ppname br in
      apply_checker_result_k r ppname in

    let br_name = if is_then then "then" else "else" in

    if hyp `Set.mem` freevars_st br
    then fail g (Some br.range)
           (Printf.sprintf "check_if: branch hypothesis is in freevars of checked %s branch" br_name)
    else (| br, c, d |)
  in

  let (| e1, c1, e1_typing |) = check_branch tm_true e1 true in
  let (| e2, c2, e2_typing |) = check_branch tm_false e2 false in    
  let (| c, e1_typing, e2_typing |) =
    combine_if_branches _ _ _ e1_typing _ _ _ e2_typing in

  let c_typing = 
    let x = fresh g in
    if x `Set.mem` freevars post //exclude this
    then fail g None "Impossible: check_if: unexpected freevar in post, please file a bug-report"
    else if not (eq_tm (comp_res c) post_hint.ret_ty &&
                 eq_univ (comp_u c) post_hint.u &&
                 eq_tm (comp_post c) post_hint.post) //exclude by check' strengthening
    then fail g None
           (Printf.sprintf "check_if: computation type after combining branches does not match post hint,\
                            computed: (%s, %s, %s), expected (%s, %s, %s)"
              (P.univ_to_string (comp_u c)) (P.term_to_string (comp_res c)) (P.term_to_string (comp_post c))
              (P.univ_to_string post_hint.u) (P.term_to_string post_hint.ret_ty) (P.term_to_string post_hint.post))
    else
        let post_typing = post_hint_typing g post_hint x in
        intro_comp_typing g c pre_typing post_typing.ty_typing x post_typing.post_typing
  in

  let d : st_typing_in_ctxt g pre (Some post_hint) =
    (| _, c, T_If g b e1 e2 c _ hyp b_typing e1_typing e2_typing (E c_typing) |) in

  checker_result_for_st_typing d res_ppname
