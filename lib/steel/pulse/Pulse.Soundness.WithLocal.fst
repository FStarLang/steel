module Pulse.Soundness.WithLocal

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module R = FStar.Reflection.V2

module PReflUtil = Pulse.Reflection.Util
module WT = Pulse.Steel.Wrapper.Typing
module LN = Pulse.Typing.LN
module FV = Pulse.Typing.FV

let mk_t_abs (g:env)
             (#ty:term)
             (t_typing:typing g ty (tm_type u_zero))
             (ppname:ppname)
             (r_t_typing:RT.tot_typing (elab_env g)
                                       (elab_term ty)
                                       (elab_comp (C_Tot (tm_type u_zero))))
             (#body:st_term)
             (#x:var { None? (lookup g x) /\ ~(x `Set.mem` freevars_st body) })
             (#c:comp)
             (#body_typing:st_typing (push_binding g x ppname ty) (open_st_term body x) c)
             (r_body_typing:RT.tot_typing (elab_env (push_binding g x ppname ty))
                                          (elab_st_typing body_typing)
                                          (elab_comp c))
  : GTot (RT.tot_typing (elab_env g)
            (mk_abs_with_name ppname.name (elab_term ty) R.Q_Explicit (RT.close_term (elab_st_typing body_typing) x))
            (elab_term (tm_arrow {binder_ty=ty;binder_ppname=ppname} None (close_comp c x))))
  = mk_t_abs g #_ #_ #_ #t_typing ppname r_t_typing r_body_typing


//TODO: this proof needs to be tamed
#push-options "--z3rlimit_factor 40 --fuel 10 --split_queries always --query_stats"
let withlocal_soundness #g #t #c d soundness =
  admit();
  let T_WithLocal _ init body init_t c x init_typing init_t_typing c_typing body_typing = d in
  let CT_ST _ st st_typing = c_typing in
  
  let rg =  elab_env g in
  let ru = comp_u c in
  let ra = elab_term init_t in
  let rinit = elab_term init in
  let rpre = elab_term (comp_pre c) in
  let rret_t = elab_term (comp_res c) in
  let rpost = mk_abs rret_t R.Q_Explicit (elab_term (comp_post c)) in
  let rbody =
    RT.mk_abs (PReflUtil.mk_ref ra) R.Q_Explicit
      (RT.subst_term (elab_st_typing body_typing) [ RT.ND x 0 ]) in
  let a_typing:RT.tot_typing rg ra (R.pack_ln (R.Tv_Type (R.pack_universe R.Uv_Zero))) =
    tot_typing_soundness init_t_typing in
  
  let rinit_typing:RT.tot_typing rg rinit ra =
    tot_typing_soundness init_typing in

  let cres_typing, cpre_typing, cpost_typing =
    Pulse.Soundness.Comp.stc_soundness st_typing in

  let pre_typing:RT.tot_typing rg rpre vprop_tm = cpre_typing in
  let ret_t_typing:RT.tot_typing rg rret_t (R.pack_ln (R.Tv_Type ru)) = cres_typing in
  let post_typing:RT.tot_typing rg rpost (mk_arrow (rret_t, R.Q_Explicit) vprop_tm) =
    cpost_typing in
  
  let elab_body_comp = elab_comp (comp_withlocal_body x init_t init c) in

  let rbody_typing
    : RT.tot_typing (elab_env (push_binding g x ppname_default (mk_ref init_t)))
                    (elab_st_typing body_typing)
                    elab_body_comp =
    soundness _ _ _ body_typing in

  let ref_init_t_typing : typing g (mk_ref init_t) (tm_type u0) =
    magic () in

  let rref_init_t_typing
    : RT.tot_typing ( elab_env g)
                    (elab_term (mk_ref init_t))
                    (elab_comp (C_Tot (tm_type u0))) = magic () in

  RT.close_term_spec (elab_st_typing body_typing) x;
  assert (RT.subst_term (elab_st_typing body_typing) [ RT.ND x 0 ] ==
          RT.close_term (elab_st_typing body_typing) x);
          
  
  let rbody_typing
    : RT.tot_typing (elab_env g)
                    rbody
                    (mk_arrow (PReflUtil.mk_ref ra, R.Q_Explicit)
                              (elab_comp (close_comp (comp_withlocal_body x init_t init c) x))) =
    coerce_eq () (
       mk_t_abs g #(mk_ref init_t) ref_init_t_typing ppname_default rref_init_t_typing #body #x #_ #body_typing rbody_typing
    )
  in
  // We now have this rbody typing,
  //   need to match it to what is expected by wrapper withlocal typing

  FV.comp_typing_freevars c_typing;
  close_comp_with_non_free_var c x 0;
  assert (close_comp c x == c);
  FV.tot_typing_freevars init_typing;
  close_with_non_freevar init x 0;
  assert (close_term init x == init);

  FV.tot_typing_freevars init_t_typing;
  close_with_non_freevar init_t x 0;
  close_with_non_freevar init_t x 1;
  close_with_non_freevar init_t x 2;
  assert (close_term' init_t x 0 == init_t);
  assert (close_term' init_t x 1 == init_t);
  assert (close_term' init_t x 2 == init_t);

  let cbody_closed = close_comp (comp_withlocal_body x init_t init c) x in

  // c1 and c2 are the two comps we need to match (prove equiv)
  let c1 = elab_comp cbody_closed in
  let c2 = mk_stt_comp ru rret_t
    (mk_star rpre (PReflUtil.mk_pts_to ra (RT.bound_var 0) full_perm_tm rinit))
    (WT.with_local_bodypost rpost ra rret_t x) in

  // try to get c1 in mk_stt_comp form,
  //   after which we will use mk_stt_comp_equiv

  let c1_pre = elab_term (tm_star (comp_pre c) (mk_pts_to init_t (null_bvar 0) init)) in
  let c1_post =
    mk_abs rret_t R.Q_Explicit
      (mk_star
         (elab_term (comp_post c))
         (elab_term
            (tm_exists_sl u0 (as_binder init_t)
               (mk_pts_to init_t (null_bvar 2) (null_bvar 0))))) in

  assert (c1 == mk_stt_comp ru rret_t c1_pre c1_post);
  assert (c1_pre == mk_star rpre (PReflUtil.mk_pts_to ra (RT.bound_var 0) full_perm_tm rinit));
  let rbody_typing
    : RT.tot_typing (elab_env g)
                    rbody
                    (mk_arrow
                       (PReflUtil.mk_ref ra, R.Q_Explicit)
                       (mk_stt_comp ru rret_t c1_pre c1_post)) =
    coerce_eq () rbody_typing in

  let rx_tm = RT.var_as_term x in

  // get WT withlocal body post in mk_star form (push close inside)
  assert (WT.with_local_bodypost_body rpost ra x ==
          PReflUtil.mk_star
            (RT.subst_term
               (R.pack_ln (R.Tv_App rpost (rx_tm, R.Q_Explicit))) [ RT.ND x 0 ])
            (RT.subst_term
               (PReflUtil.mk_exists (R.pack_universe R.Uv_Zero) ra
                  (PReflUtil.mk_abs ra R.Q_Explicit
                     (PReflUtil.mk_pts_to ra (RT.bound_var 2) full_perm_tm (RT.bound_var 0))))
               [ RT.ND x 0 ]));

  let y = fresh g in
  let g_y = RT.extend_env (elab_env g) y (PReflUtil.mk_ref ra) in

  // pre equiv is easy, refl
  let pre_equiv
    : RT.equiv g_y
        (RT.subst_term c1_pre (RT.open_with_var y 0))
        (RT.subst_term
           (mk_star rpre (PReflUtil.mk_pts_to ra (RT.bound_var 0) full_perm_tm rinit))
           (RT.open_with_var y 0)) = RT.EQ_Refl _ _ in

  let z = fresh (push_binding g y ppname_default (mk_ref init_t)) in
  let g_z = RT.extend_env g_y z (RT.subst_term rret_t (RT.open_with_var y 0)) in
  assume (None? (RT.lookup_bvar g_y z));

  RT.well_typed_terms_are_ln _ _ _ post_typing;
  assert (RT.ln' (elab_term (comp_post c)) 0);

  // post is of the star form, we will show component-wise equiv
  let postl_equiv
    : RT.equiv g_z
        (RT.subst_term
           (RT.subst_term
              (elab_term (comp_post c))
              (RT.open_with_var y 1))
           (RT.open_with_var z 0))
        (RT.subst_term
           (RT.subst_term
              (RT.subst_term
                 (R.pack_ln (R.Tv_App rpost (rx_tm, R.Q_Explicit)))
                 [ RT.ND x 0 ])
              (RT.open_with_var y 1))
           (RT.open_with_var z 0)) =

    // x is not free in g, and rpost is well-typed in g
    // so x is not free in rpost, see RT.close_with_not_free_var
    assume (RT.subst_term rpost [ RT.ND x 0 ] == rpost);

    // rret_t is well-typed in g, hence ln,
    // hence opening index 1 should give the same term, see RT.open_with_gt_ln
    assume (RT.subst_term rret_t (RT.open_with_var y 1) == rret_t);

    // same argument, rpost is well-typed, hence ln, hence RT.open_with_gt_ln
    assume (RT.subst_term rpost (RT.open_with_var z 0) == rpost);
    let d : RT.equiv g_z
              (RT.subst_term (elab_term (comp_post c)) (RT.open_with_var z 0))
              (R.pack_ln (R.Tv_App rpost ((RT.var_as_term z), R.Q_Explicit))) =      
      RT.EQ_Sym _ _ _
        (RT.EQ_Beta _ rret_t R.Q_Explicit
           (elab_term (comp_post c))
           (RT.var_as_term z)) in
    d
  in

  let postr_equiv
    : RT.equiv g_z
        (RT.subst_term
           (RT.subst_term
              (elab_term (tm_exists_sl u0 (as_binder init_t)
                           (mk_pts_to init_t (null_bvar 2) (null_bvar 0))))
              (RT.open_with_var y 1))
           (RT.open_with_var z 0))
        (RT.subst_term
           (RT.subst_term
              (RT.subst_term
                 (PReflUtil.mk_exists (R.pack_universe R.Uv_Zero) ra
                    (mk_abs ra R.Q_Explicit
                       (PReflUtil.mk_pts_to ra
                          (RT.bound_var 2)
                          full_perm_tm
                          (RT.bound_var 0))))
                 [ RT.ND x 0 ])
              (RT.open_with_var y 1))
           (RT.open_with_var z 0)) =

    // ra is well-typed in g, and x is not in g
    assume (~ (x `Set.mem` RT.freevars ra));
    RT.close_with_not_free_var ra x 0;
    RT.close_with_not_free_var ra x 1;
    RT.EQ_Refl _ _
  in

  let post_equiv
    : RT.equiv g_z _ _ =
    mk_star_equiv _ _ _ _ _ postl_equiv postr_equiv in

  let post_equiv
    : RT.equiv g_y
        (mk_abs (RT.subst_term rret_t (RT.open_with_var y 0)) R.Q_Explicit
          (mk_star
             (RT.subst_term
                (elab_term (comp_post c))
                (RT.open_with_var y 1))
             (RT.subst_term
                (elab_term (tm_exists_sl u0 (as_binder init_t)
                              (mk_pts_to init_t (null_bvar 2) (null_bvar 0))))
                (RT.open_with_var y 1))))
        (mk_abs (RT.subst_term rret_t (RT.open_with_var y 0)) R.Q_Explicit
           (RT.subst_term
              (WT.with_local_bodypost_body rpost ra x)
              (RT.open_with_var y 1))) =
    RT.equiv_abs _ _ z post_equiv in

  let post_equiv
    : RT.equiv g_y
        (RT.subst_term c1_post (RT.open_with_var y 0))
        (RT.subst_term
           (WT.with_local_bodypost rpost ra rret_t x)
           (RT.open_with_var y 0)) = post_equiv in

  let arrow_codom_equiv
    : RT.equiv g_y
        (RT.subst_term
           (mk_stt_comp ru rret_t c1_pre c1_post)
           (RT.open_with_var y 0))
        (RT.subst_term
           (mk_stt_comp ru rret_t
              (mk_star rpre (PReflUtil.mk_pts_to ra (RT.bound_var 0) full_perm_tm rinit))
              (WT.with_local_bodypost rpost ra rret_t x))
           (RT.open_with_var y 0)) =
    PReflUtil.mk_stt_comp_equiv _ ru
      (RT.subst_term rret_t (RT.open_with_var y 0)) _ _ _ _
      pre_equiv post_equiv in

  let arrow_equiv
    : RT.equiv (elab_env g)
        (mk_arrow
           (PReflUtil.mk_ref ra, R.Q_Explicit)
           (mk_stt_comp ru rret_t c1_pre c1_post))
        (mk_arrow
           (PReflUtil.mk_ref ra, R.Q_Explicit)
           (mk_stt_comp ru rret_t
              (mk_star rpre (PReflUtil.mk_pts_to ra (RT.bound_var 0) full_perm_tm rinit))
              (WT.with_local_bodypost rpost ra rret_t x))) =
    RT.equiv_arrow _ _ _ arrow_codom_equiv in

  let rbody_typing
    : RT.tot_typing
        ( elab_env g)
        rbody
        (mk_arrow
           (PReflUtil.mk_ref ra, R.Q_Explicit)
           (mk_stt_comp ru rret_t
              (mk_star rpre (PReflUtil.mk_pts_to ra (RT.bound_var 0) full_perm_tm rinit))
              (WT.with_local_bodypost rpost ra rret_t x))) =
    RT.T_Sub _ _ _ _ rbody_typing
      (RT.Relc_typ _ _ _ _ _ (RT.Rel_equiv _ _ _ _ arrow_equiv)) in

  WT.with_local_typing x a_typing rinit_typing pre_typing ret_t_typing post_typing rbody_typing
