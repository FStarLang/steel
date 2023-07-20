module Pulse.Checker.Common
module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing
module Metatheory = Pulse.Typing.Metatheory
module CP = Pulse.Checker.Pure
module RU = Pulse.RuntimeUtils
module FV = Pulse.Typing.FV
module P = Pulse.Syntax.Printer

open Pulse.Typing.Combinators

let format_failed_goal (g:env) (ctxt:list term) (goal:list term) =
  let terms_to_strings (ts:list term)= T.map Pulse.Syntax.Printer.term_to_string ts in
  let numbered_list ss = 
       let _, s = T.fold_left (fun (i, acc) s -> (i+1, Printf.sprintf "%d. %s" i s :: acc)) (1, []) ss in
       String.concat "\n  " (List.rev s)
  in
  let format_terms (ts:list term) = numbered_list (terms_to_strings ts) in
  Printf.sprintf 
    "Failed to prove the following goals:\n  \
     %s\n\
     The remaining conjuncts in the separation logic context available for use are:\n  \
     %s\n\
     The typing context is:\n  \
     %s\n"
    (format_terms goal)
    (format_terms ctxt)
    (env_to_string g)


let mk_arrow ty t = RT.mk_arrow (elab_term ty) T.Q_Explicit (elab_term t)
let mk_abs ty t = RT.(mk_abs (elab_term ty) T.Q_Explicit (elab_term t))

let post_typing_as_abstraction (#g:env) (#x:var) (#ty:term) (#t:term { fresh_wrt x g (freevars t) })
                               (_:tot_typing (push_binding g x ppname_default ty) (open_term t x) tm_vprop)
  : FStar.Ghost.erased (RT.tot_typing (elab_env g) (mk_abs ty t) (mk_arrow ty tm_vprop))                                 
  = admit()

let intro_post_hint g ret_ty_opt post =
  let x = fresh g in
  let ret_ty = 
      match ret_ty_opt with
      | None -> tm_fstar RT.unit_ty FStar.Range.range_0
      | Some t -> t
  in
  let ret_ty, _ = CP.instantiate_term_implicits g ret_ty in
  let (| u, ty_typing |) = CP.check_universe g ret_ty in
  let (| post, post_typing |) = CP.check_vprop (push_binding g x ppname_default ret_ty) (open_term_nv post (v_as_nv x)) in 
  let post' = close_term post x in
  Pulse.Typing.FV.freevars_close_term post x 0;
  assume (open_term post' x == post);
  { g; ret_ty; u; ty_typing; post=post'; post_typing=post_typing_as_abstraction #_ #_ #_ #post' post_typing }

let post_hint_from_comp_typing #g #c ct = 
  let st_comp_typing = Metatheory.comp_typing_inversion ct in
  let (| ty_typing, pre_typing, x, post_typing |) = Metatheory.st_comp_typing_inversion st_comp_typing in
  let p : post_hint_t = 
    { g; ret_ty = comp_res c; u=comp_u c; 
      ty_typing=ty_typing;
      post=comp_post c;
      post_typing=post_typing_as_abstraction post_typing }
  in
  p

// let try_frame_pre (#g:env)
//                   (#t:st_term)
//                   (#pre:term)
//                   (pre_typing: tot_typing g pre tm_vprop)
//                   (#c:comp_st)
//                   (t_typing: st_typing g t c)
//   : T.Tac (c':comp_st { comp_pre c' == pre } &
//            st_typing g t c')
//   = let g = CP.push_context "try_frame_pre" t.range g in
//     if RU.debug_at_level (fstar_env g) "try_frame"
//     then T.print (Printf.sprintf "(Try frame@%s) with %s\n\tcomp=%s,\n\tpre=%s\n"
//                                  (T.range_to_string t.range)
//                                  (print_context g)
//                                  (P.comp_to_string c)
//                                  (P.term_to_string pre));
//     match Pulse.Checker.Framing.try_frame_pre #g pre_typing t_typing with
//     | Inl ok -> ok
//     | Inr fail -> T.raise (Framing_failure fail)

let k_elab_unit (g:env) (ctxt:term)
  : continuation_elaborator g ctxt g ctxt
  = fun p r -> r

let k_elab_trans
  (#g0:env) (#g1:env { g1 `env_extends` g0 }) (#g2:env { g2 `env_extends` g1 }) (#ctxt0 #ctxt1 #ctxt2:term)
  (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
  (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2
   = fun post_hint res -> k0 post_hint (k1 post_hint res)

let comp_st_with_post (c:comp_st) (post:term)
  : c':comp_st { st_comp_of_comp c' == ({ st_comp_of_comp c with post} <: st_comp) } =
  match c with
  | C_ST st -> C_ST { st with post }
  | C_STGhost i st -> C_STGhost i { st with post }
  | C_STAtomic i st -> C_STAtomic i {st with post}

let ve_unit_r g (p:term) : vprop_equiv g (tm_star p tm_emp) p = 
  VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _)

let st_equiv_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                  (post:term { freevars post `Set.subset` freevars (comp_post c)})
                  (veq: (x:var { fresh_wrt x g (freevars (comp_post c)) } ->
                         vprop_equiv (push_binding g x ppname_default (comp_res c)) 
                                     (open_term (comp_post c) x)
                                     (open_term post x)))
  : st_typing g t (comp_st_with_post c post)
  = let c' = comp_st_with_post c post in
    let (| u_of, pre_typing, x, post_typing |) = Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness d))) in
    let veq = veq x in
    let st_equiv : st_equiv g c c' =
        ST_VPropEquiv g c c' x pre_typing u_of post_typing (VE_Refl _ _) veq
    in
    T_Equiv _ _ _ _ d st_equiv

let simplify_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                  (post:term { comp_post c == tm_star post tm_emp})
  : st_typing g t (comp_st_with_post c post)
  = st_equiv_post d post (fun x -> ve_unit_r (push_binding g x ppname_default (comp_res c)) (open_term post x))

let simplify_lemma (c:comp_st) (c':comp_st) (post_hint:option post_hint_t)
  : Lemma
    (requires
        comp_post_matches_hint c post_hint /\
        comp_res c' == comp_res c /\
        comp_u c' == comp_u c /\
        comp_post c' == tm_star (comp_post c) tm_emp)
    (ensures comp_post_matches_hint (comp_st_with_post c' (comp_post c)) post_hint /\
             comp_pre (comp_st_with_post c' (comp_post c)) == comp_pre c')
  = () 

let vprop_equiv_typing_bk (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_vprop)
                           (#p:_) (d:vprop_equiv g p ctxt)
  : tot_typing g p tm_vprop 
  = let _, bk = vprop_equiv_typing d in
    bk ctxt_typing


#push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 0"
let k_elab_equiv_continutation (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt #ctxt1 #ctxt2:term)
  (k:continuation_elaborator g1 ctxt g2 ctxt1)
  (d:vprop_equiv g2 ctxt1 ctxt2)
  : continuation_elaborator g1 ctxt g2 ctxt2 =
  fun post_hint res ->
  let framing_token : frame_for_req_in_ctxt g2 ctxt1 ctxt2 =
    let d : vprop_equiv g2 (tm_star ctxt2 tm_emp) ctxt1 = 
      VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Trans _ _ _ _ (VE_Unit _ _) (VE_Sym _ _ _ d)) in
      (| tm_emp, emp_typing, d |)
  in
  let (| st, c, st_d |) = res in
  if not (stateful_comp c) then k post_hint (| st, c, st_d |)
  else
    let (| _, pre_typing, _, _ |) =
      Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness st_d))) in
    let (| c', st_d' |) =
      apply_frame (vprop_equiv_typing_bk pre_typing d) st_d framing_token in
    assert (comp_post c' == tm_star (comp_post c) tm_emp);
    let st_d' = simplify_post st_d' (comp_post c) in
    k post_hint (| st, _, st_d' |)
#pop-options

let vprop_equiv_typing_fwd (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_vprop)
                           (#p:_) (d:vprop_equiv g ctxt p)
  : tot_typing g p tm_vprop 
  = let fwd, _ = vprop_equiv_typing d in
    fwd ctxt_typing

#push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 0"
let k_elab_equiv_prefix
  (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt1 #ctxt2 #ctxt:term)
  (k:continuation_elaborator g1 ctxt1 g2 ctxt)
  (d:vprop_equiv g1 ctxt1 ctxt2)
  : continuation_elaborator g1 ctxt2 g2 ctxt =
  fun post_hint res ->
  let framing_token : frame_for_req_in_ctxt g1 ctxt2 ctxt1 = 
  let d = VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Trans _ _ _ _ (VE_Unit _ _) d) in
    (| tm_emp, emp_typing, d |)
  in
  let res = k post_hint res in
  let (| st, c, st_d |) = res in
  if not (stateful_comp c) then (| st, c, st_d |)
  else let (| _, pre_typing, _, _ |) =
         Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness st_d))) in
       let (| c', st_d' |) =
         apply_frame
           (vprop_equiv_typing_fwd pre_typing d)
           st_d
           framing_token in
        simplify_lemma c c' post_hint;
        let c''  = comp_st_with_post c' (comp_post c) in
        let st_d' : st_typing g1 st c'' = simplify_post st_d' (comp_post c) in
        let res : st_typing_in_ctxt g1 ctxt2 post_hint = (| st, c'', st_d' |) in
        res
#pop-options

let k_elab_equiv
  (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt1 #ctxt1' #ctxt2 #ctxt2':term)                 
  (k:continuation_elaborator g1 ctxt1 g2 ctxt2)
  (d1:vprop_equiv g1 ctxt1 ctxt1')
  (d2:vprop_equiv g2 ctxt2 ctxt2')
  : continuation_elaborator g1 ctxt1' g2 ctxt2' =
  
  let k : continuation_elaborator g1 ctxt1 g2 ctxt2' =
    k_elab_equiv_continutation k d2 in
  let k : continuation_elaborator g1 ctxt1' g2 ctxt2' =
    k_elab_equiv_prefix k d1 in
  k

#push-options "--query_stats --fuel 2 --ifuel 2 --split_queries no --z3rlimit_factor 20"
let continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (tm_star ctxt (comp_pre c1)) tm_vprop)
  (x:var { None? (lookup g x) })
  : T.Tac (continuation_elaborator
             g (tm_star ctxt (comp_pre c1))
             (push_binding g x ppname_default (comp_res c1)) (tm_star (open_term (comp_post c1) x) ctxt)) =

  let pre1 = comp_pre c1 in
  let res1 = comp_res c1 in
  let post1 = comp_post c1 in
  let ctxt_typing = star_typing_inversion_l ctxt_pre1_typing in
  // let p_prop = Metatheory.pure_typing_inversion pure_typing in
  let v_eq = VE_Comm g ctxt pre1 in
  let framing_token : frame_for_req_in_ctxt g (tm_star ctxt pre1) pre1 = 
    (| ctxt, ctxt_typing, VE_Comm g pre1 ctxt  |)
  in
  let (| c1, e1_typing |) =
    apply_frame ctxt_pre1_typing e1_typing framing_token in
  let (| u_of_1, pre_typing, _, _ |) =
    Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness e1_typing))) in
  let b = res1 in
  let g' = push_binding g x ppname_default b in
  
  let post1_opened = open_term_nv post1 (v_as_nv x) in
  let k : continuation_elaborator g (tm_star ctxt pre1) g' (tm_star post1_opened ctxt) =
    fun post_hint res ->
    let (| e2, c2, e2_typing |) = res in
    if not (stateful_comp c2) // || None? post_hint
    then T.fail "Unexpected non-stateful comp in continuation elaborate"
    else (
      let e2_typing : st_typing g' e2 c2 = e2_typing in
      let e2_closed = close_st_term e2 x in
      assume (open_st_term e2_closed x == e2);
      assert (comp_pre c1 == (tm_star ctxt pre1));
      assert (comp_post c1 == tm_star post1 ctxt);
      assert (comp_pre c2 == tm_star post1_opened ctxt);
      assert (open_term (comp_post c1) x == tm_star post1_opened (open_term ctxt x));
      // ctxt is well-typed, hence ln
      assume (open_term ctxt x == ctxt);
      assert (open_term (comp_post c1) x == comp_pre c2);
      // we closed e2 with x
      assume (~ (x `Set.mem` freevars_st e2_closed));
      if x `Set.mem` freevars (comp_post c2)
      then T.fail "Impossible"
      else (
        let t_typing, post_typing =
          Pulse.Typing.Combinators.bind_res_and_post_typing g (st_comp_of_comp c2) x post_hint in
        let (| e, c, e_typing |) =
          Pulse.Typing.Combinators.mk_bind
            g (tm_star ctxt pre1) 
            e1 e2_closed c1 c2 (v_as_nv x) e1_typing
            u_of_1 
            e2_typing
            t_typing
            post_typing
        in
        (| e, c, e_typing |)
      )
    )

  in
  k
#pop-options

let rec check_equiv_emp (g:env) (vp:term)
  : option (vprop_equiv g vp tm_emp)
  = match vp.t with
    | Tm_Emp -> Some (VE_Refl _ _)
    | Tm_Star vp1 vp2 ->
      (match check_equiv_emp g vp1, check_equiv_emp g vp2 with
       | Some d1, Some d2 ->
         let d3 : vprop_equiv g (tm_star vp1 vp2) (tm_star tm_emp tm_emp)
           = VE_Ctxt _ _ _ _ _ d1 d2 in
         let d4 : vprop_equiv g (tm_star tm_emp tm_emp) tm_emp =
           VE_Unit _ _ in
         Some (VE_Trans _ _ _ _ d3 d4)
       | _, _ -> None)
     | _ -> None


// #push-options "--z3rlimit_factor 2"
// let replace_equiv_post
//       (r:range)
//       (g:env)
//       (c:comp{stateful_comp c /\ freevars_comp c `Set.subset` FV.vars_of_env g})
//       (ct:Metatheory.comp_typing_u g c)
//       (post_hint:post_hint_opt g)
//   : T.Tac (c1:comp { stateful_comp c1 /\ comp_pre c1 == comp_pre c /\ comp_post_matches_hint c1 post_hint } &
//            st_equiv g c c1)
//   = let g = CP.push_context "replace_equiv_post" r g in
//     let {u=u_c;res=res_c;pre=pre_c;post=post_c} = st_comp_of_comp c in
//     let st_typing = Metatheory.comp_typing_inversion ct in
//     let (| res_c_typing, pre_c_typing, x, post_c_typing |) = Metatheory.st_comp_typing_inversion st_typing in
//     let px = v_as_nv x in
//     let g_post = push_binding g x (fst px) res_c in
//     let post_c_opened = open_term_nv post_c px in
//     match post_hint with
//     | None ->
//       (| c,
//          ST_VPropEquiv
//            g c c x pre_c_typing res_c_typing post_c_typing
//            (VE_Refl _ _)
//            (VE_Refl _ _) |)
//     | Some post ->
//       if not (eq_univ u_c post.u &&
//               eq_tm res_c post.ret_ty)
//       then fail g None 
//             (Printf.sprintf "(%s) Inferred result type does not match annotation.\n\
//                              Expected type %s\n\
//                              Got type %s\n"
//                   (T.range_to_string r)
//                   (P.term_to_string post.ret_ty)
//                   (P.term_to_string res_c))
//       else if (x `Set.mem` freevars post.post)
//       then fail g None "Unexpected variable clash with annotated postcondition"
//       else (
//         let post_opened = open_term_nv post.post px in
//         let post_c_post_eq
//           : vprop_equiv g_post post_c_opened post_opened
//           = Pulse.Checker.Framing.check_vprop_equiv
//               (CP.push_context "check_vprop_equiv" r g_post)
//               post_c_opened
//               post_opened
//               post_c_typing
//         in
//         let st_comp_with_post : st_comp = {
//           u=u_c;
//           res=res_c;
//           pre=pre_c;
//           post=close_term post_opened x
//         } in
//         let c_with_post = c `with_st_comp` st_comp_with_post in
//         assume (close_term post_opened x == post.post);
//         assume (open_term (close_term post_opened x) x == post_opened);
//         (| c_with_post,
//            ST_VPropEquiv
//              g c c_with_post x pre_c_typing res_c_typing post_c_typing
//              (VE_Refl _ _)
//              post_c_post_eq |)
//       )
// #pop-options

// let repack (#g:env) (#pre:term) (#t:st_term)
//            (x:(c:comp_st { comp_pre c == pre } & st_typing g t c))
//            (post_hint:post_hint_opt g)
//   : T.Tac (checker_result_t g pre post_hint true)
//   = let (| c, d_c |) = x in
//     if stateful_comp c
//     then (
//       FV.st_typing_freevars d_c;
//       let (| c1, c_c1_eq |) = replace_equiv_post t.range g c (Metatheory.st_typing_correctness d_c) post_hint in
//       (| t, c1, T_Equiv _ _ _ _ d_c c_c1_eq |)
//     )
//     else (| t, c, d_c |)

let intro_comp_typing (g:env) 
                      (c:comp_st)
                      (pre_typing:tot_typing g (comp_pre c) tm_vprop)
                      (res_typing:universe_of g (comp_res c) (comp_u c))
                      (x:var { fresh_wrt x g (freevars (comp_post c)) })
                      (post_typing:tot_typing (push_binding g x ppname_default (comp_res c)) (open_term (comp_post c) x) tm_vprop)
  : T.Tac (comp_typing g c (comp_u c))
  = let intro_st_comp_typing (st:st_comp { comp_u c == st.u /\
                                           comp_pre c == st.pre /\
                                           comp_res c == st.res /\
                                           comp_post c == st.post } )
      : T.Tac (st_comp_typing g st)
      = STC g st x res_typing pre_typing post_typing
    in
    match c with
    | C_ST st -> 
      let stc = intro_st_comp_typing st in
      CT_ST _ _ stc
    | C_STAtomic i st -> 
      let stc = intro_st_comp_typing st in
      let (| ty, i_typing |) = CP.core_check_term g i in
      if not (eq_tm ty tm_inames)
      then fail g None "Ill-typed inames"
      else CT_STAtomic _ _ _ (E i_typing) stc
    | C_STGhost i st -> 
      let stc = intro_st_comp_typing st in
      let (| ty, i_typing |) = CP.core_check_term g i in
      if not (eq_tm ty tm_inames)
      then fail g None "Ill-typed inames"
      else CT_STGhost _ _ _ (E i_typing) stc

let return_in_ctxt (g:env) (y:var) (u:universe) (ty:term) (ctxt:vprop)
  (ty_typing:universe_of g ty u)
  (post_hint0:post_hint_opt g { Some? post_hint0 /\ x_t_ctxt_match_post_hint g post_hint0 y ty ctxt})

  : Pure (st_typing_in_ctxt g ctxt post_hint0)
         (requires lookup g y == Some ty)
         (ensures fun _ -> True) =

  let Some post_hint = post_hint0 in

  let x = fresh g in
  assume (~ (x `Set.mem` freevars post_hint.post));
  let d = T_Return g STT false u ty (null_var y) post_hint.post x ty_typing
    (magic ())  // that null_var y is well typed at ty in g, we know since lookup g y == Some ty
    (magic ())  // typing of (open post x) in (g, x) ... post_hint is well-typed, so should get
  in
  let t = wr (Tm_Return {ctag=STT;insert_eq=false;term=null_var y}) in
  let c = comp_return STT false u ty (null_var y) post_hint.post x in
  let d : st_typing g t c = d in

  let _ :squash (comp_pre c == ctxt /\ comp_post_matches_hint c (Some post_hint)) =
    match post_hint0 with
    | Some post_hint ->
      // this u should follow from equality of t
      assume (comp_u c == post_hint.u) in

  (| _, _, d |)

let apply_checker_result_k (#g:env) (#ctxt:vprop) (#post_hint:post_hint_for_env g)
  (r:checker_result_t g ctxt (Some post_hint))
  : T.Tac (st_typing_in_ctxt g ctxt (Some post_hint)) =

  // TODO: FIXME add to checker result type?
  let (| y, ty_y, pre', g1, k |) = r in

  let (| u_ty_y, d_ty_y |) = Pulse.Checker.Pure.check_universe g1 ty_y in

  let d : st_typing_in_ctxt g1 pre' (Some post_hint) =
    return_in_ctxt g1 y u_ty_y ty_y pre' d_ty_y (Some post_hint) in

  k (Some post_hint) d

#push-options "--z3rlimit_factor 2 --fuel 0 --ifuel 1"
let checker_result_for_st_typing (#g:env) (#ctxt:vprop) (#post_hint:post_hint_opt g)
  (d:st_typing_in_ctxt g ctxt post_hint)
  : T.Tac (checker_result_t g ctxt post_hint) =

  let (| t, c, d |) = d in
 
  if not (stateful_comp c)
  then fail g None "checker_result_for_st_typing: not a stateful comp";


  let x = fresh g in

  let g' = push_binding g x ppname_default (comp_res c) in
  let ctxt' = open_term_nv (comp_post c) (ppname_default, x) in
  let k
    : continuation_elaborator
        g (tm_star tm_emp (comp_pre c))
        g' (tm_star ctxt' tm_emp) =
    continuation_elaborator_with_bind tm_emp d (magic ()) x in
  let k
    : continuation_elaborator g (comp_pre c) g' ctxt' =
    k_elab_equiv k (magic ()) (magic ()) in

  let _ : squash (checker_res_matches_post_hint g post_hint x (comp_res c) ctxt') =
    match post_hint with
    | None -> ()
    | Some post_hint -> () in

  assert (g' `env_extends` g);

  (| x, comp_res c, ctxt', g', k |)
#pop-options
