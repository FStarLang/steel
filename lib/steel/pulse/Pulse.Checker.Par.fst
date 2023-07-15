module Pulse.Checker.Par

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common
open Pulse.Checker.Comp
open Pulse.Syntax.Printer

open FStar.Printf

module FV = Pulse.Typing.FV
module MT = Pulse.Typing.Metatheory

let print_term (t: term): T.Tac unit
  = T.print (term_to_string t)

let rec print_list_terms' (l: list term): T.Tac unit
= match l with
| [] -> T.print "]"
| t::q -> (T.print ", "; print_term t; print_list_terms' q)

let print_list_terms (l: list term): T.Tac unit
  = match l with
  | [] -> T.print "[]"
  | t::q -> (T.print "["; print_term t; print_list_terms' q)

let indent (level:string) = level ^ " "

let st_equiv_to_string (#g: env) #c1 #c2 (level: string) (eq: st_equiv g c1 c2)
  : T.Tac string
  = (*if comp_pre c1 = comp_pre c2 && comp_post c1 = comp_post c2
    then T.print "Trivial equivalence!"
    else T.print "Somehow non-trivial equivalence...";*)
    sprintf "st_equiv\n%s pre1: %s\n%s pre2: %s\n%s post1: %s\n%s post2: %s"
  //pre: (%s) (%s)) (post: (%s) (%s))"
  level
  (term_to_string (comp_pre c1))
  level
  (term_to_string (comp_pre c2))
  level
  (term_to_string (comp_post c1))
  level
  (term_to_string (comp_post c2))

let rec st_typing_to_string' (#g:env) (#t:st_term) (#c:comp_st) (level: string) (ty: st_typing g t c)
//let rec st_typing_to_string (ty: st_typing)
  : T.Tac string
  = match ty with
    | T_Abs g x q b u body c _ _ -> "T_Abs"
    | T_STApp g head _ q res arg _ _ -> "T_STapp"
    | T_Return g c use_eq u t e post x _ _ _ -> "T_Return"
    | T_Lift g e c1 c2 _ _ -> "T_Lift"
    | T_Bind g e1 e2 c1 c2 b x c ty1 _ ty2 _ ->
      sprintf "T_Bind \n (%s); \n (%s)"
      (st_typing_to_string' (indent level) ty1)
      (st_typing_to_string' (indent level) ty2)
    | T_TotBind g e1 e2 t1 c2 x _ ty' ->
      sprintf "T_TotBind (%s)"
      (st_typing_to_string' (indent level) ty')
    | T_Frame g e c frame _ ty' ->
      sprintf "T_Frame (frame=%s) (\n%s%s)"
      (term_to_string frame)
      level
      (st_typing_to_string' (indent level) ty')
    | T_Equiv g e c c' ty' equiv ->
      sprintf "T_Equiv (%s) (\n%s%s)"
      //(st_equiv_to_string level equiv)
      "..."
      level
      (st_typing_to_string' (indent level) ty')
    | T_Par g eL cL eR cR x _ _ ty1 ty2 -> "T_Par"
    | _ -> "Unsupported"
    // TODO: If

let st_typing_to_string (#g:env) (#t:st_term) (#c:comp_st) (ty: st_typing g t c)
  = st_typing_to_string' #g #t #c "" ty
//let st_typing_to_string #g #t #c (ty: st_typing g t c) = st_typing_to_string' "" ty

// Would need a stronger postcondition
// Like pre and post are equiv
let create_st_equiv (g: env) (c: comp_st) (c': comp_st)
: st_equiv g c c'
= let x = fresh g in
  assume ( ~(x `Set.mem` freevars (comp_post c)) /\
          ~(x `Set.mem` freevars (comp_post c')) );
  assume false;
  ST_VPropEquiv g c c' x (magic()) (magic()) (magic()) (magic()) (magic())

// This function replaces T_Frame with empty frames by T_Equiv
let rec replace_frame_emp_with_equiv #g #t #c (ty: st_typing g t c):
  Tot (st_typing g t c) (decreases ty)
  = match ty with
  | T_Frame g e c' frame tot_ty ty' -> 
  // c = add_frame c'
  if Tm_Emp? frame.t
    then let st_eq: st_equiv g c' c = create_st_equiv g c' c in
      T_Equiv g e c' c (replace_frame_emp_with_equiv ty') st_eq
    else ty
  | T_Equiv g e c c' ty' equiv ->
  T_Equiv g e c c' (replace_frame_emp_with_equiv ty') equiv
  | T_Bind g e1 e2 c1 c2 b x c ty1 tot1 ty2 tot2 ->
  T_Bind g e1 e2 c1 c2 b x c (replace_frame_emp_with_equiv ty1) tot1 (replace_frame_emp_with_equiv ty2) tot2
  | _ -> ty

// This function collapses two consecutive nested T_Equiv into one
let rec collapse_equiv #g #e #c (ty: st_typing g e c):
  //Tot (st_typing g e c) (decreases ty)
  T.Tac (st_typing g e c)
  = match ty with
  // Pattern: T_Equiv g e c' c ...
  | T_Equiv _ _ c' _ (T_Equiv _ _ c'' _ ty' eq') eq ->
  let st_eq: st_equiv g c'' c = create_st_equiv g c'' c in
  collapse_equiv (T_Equiv g e c'' c ty' st_eq)
  | T_Equiv _ _ c' _ ty' eq -> T_Equiv g e c' c (collapse_equiv ty') eq
  | T_Bind g e1 e2 c1 c2 b x c ty1 tot1 ty2 tot2 ->
  T_Bind g e1 e2 c1 c2 b x c (collapse_equiv ty1) tot1 (collapse_equiv ty2) tot2
  | _ -> ty

let rec collect_frames #g #e #c (ty: st_typing g e c):
  T.Tac (list term)
= match ty with
  | T_Frame g e c' frame tot_ty ty' -> [frame]
  | T_Equiv g e c c' ty' equiv -> collect_frames ty'
  | T_Bind g e1 e2 c1 c2 b x c ty1 tot1 ty2 tot2 -> collect_frames ty1 @ collect_frames ty2
  | _ -> T.fail "Unable to figure out frame at this leaf"
 
let simplify_st_typing #g #e #c (ty: st_typing g e c): T.Tac (st_typing g e c)
  = collapse_equiv (replace_frame_emp_with_equiv ty)

// Soundness: true ==> it is
// (false means we didn't find it, not that it's not there)
let rec is_host_term_in_vprop (ft: host_term) (t: term)
  = match t.t with
  | Tm_FStar ht -> Reflection.term_eq ft ht
  | Tm_Star l r -> is_host_term_in_vprop ft l || is_host_term_in_vprop ft r
  | _ -> false

let rec compute_intersection (t1: term) (t2: term) =
  match t1.t with
  | Tm_FStar ft -> if is_host_term_in_vprop ft t2 then [ft] else []
  | Tm_Star l r -> compute_intersection l t2 @ compute_intersection r t2
  | _ -> []

let rec list_of_FStar_term_to_string l: T.Tac string
= match l with
  | [] -> ""
  | t::q -> T.term_to_string t ^ ", " ^ list_of_FStar_term_to_string q

// let rec compute_intersection_of_list_host

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
  (assume false;
    let g = push_context "check_par" t.range g in
    let Tm_Par {pre1=preL; body1=eL; post1=postL;
                pre2=preR; body2=eR; post2=postR} = t.term in
// Step 1: Type left branch in full context
  let postL_hint = (if Tm_Unknown? postL.t then None else Some (intro_post_hint g None postL)) in
  //let (| eL_t, cL_t, eL_typing_t |) = check' allow_inst g eR pre pre_typing postL_hint in
  let (| eL_t, cL_t, eL_typing_t |) = check' allow_inst g eR pre pre_typing postL_hint in
  (T.print "Typechecked left branch with whole context!";
  let ty = simplify_st_typing eL_typing_t in
  let l = collect_frames ty in
  ((
  match l with
  | t1::(t2::[]) ->
  T.print "Computed intersection: ";
  T.print (list_of_FStar_term_to_string (compute_intersection t1 t2));
  T.print "End of intersection"
  | _ -> T.print "Does not have two elements..."
  );
  print_list_terms l; T.print (st_typing_to_string ty));
    let (new_preL, new_preR): term & term =
  (
    if Tm_STApp? eL.term && Tm_Unknown? preL.t
    then let Tm_STApp { head; arg_qual=qual; arg } = eL.term in
    //let g = push_context "st_app" head.range g in        
    let (| head, ty_head, dhead |) = check_term g head in
    match is_arrow ty_head with
    | Some ({binder_ty=formal;binder_ppname=ppname}, bqual, comp_typ) ->
    (
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
  //let postL_hint = (if Tm_Unknown? postL.t then None else Some (intro_post_hint g None postL)) in
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
  )))
#pop-options