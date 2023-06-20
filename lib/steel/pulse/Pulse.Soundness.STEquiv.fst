module Pulse.Soundness.STEquiv
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common
open Pulse.Checker.VPropEquiv


let stt_vprop_equiv_closing (t0 t1:R.term) (x:var)
  : Lemma (RT.close_term (stt_vprop_equiv t0 t1) x ==
           stt_vprop_equiv (RT.close_term t0 x) (RT.close_term t1 x))
           [SMTPat (RT.close_term (stt_vprop_equiv t0 t1) x)]
  = RT.close_term_spec (stt_vprop_equiv t0 t1) x;
    RT.close_term_spec t0 x;
    RT.close_term_spec t1 x

let app0 t = R.mk_app t [bound_var 0, R.Q_Explicit]

let abs_and_app0 (ty:R.term) (b:R.term) =
    R.mk_app (mk_abs ty R.Q_Explicit b) [bound_var 0, R.Q_Explicit]


// x:ty -> vprop_equiv p q ~ x:ty -> vprop_equiv ((fun y -> p) x) ((fun y -> q) x)
let stt_vprop_equiv_abstract (#g:stt_env) (#post0 #post1:term) (#pf:_) (#ty:_)
                             (d:RT.tot_typing (elab_env g) pf 
                                  (mk_arrow (ty, R.Q_Explicit)
                                     (stt_vprop_equiv (elab_term post0) (elab_term post1))))
  : GTot (RT.tot_typing (elab_env g) pf
            (mk_arrow (ty, R.Q_Explicit)
                      (stt_vprop_equiv (abs_and_app0 ty (elab_term post0))
                                       (abs_and_app0 ty (elab_term post1)))))
  = admit()

let inst_intro_vprop_post_equiv (#g:R.env) (#ty:R.term) (#u:_)
                                (d_ty:RT.tot_typing g ty (RT.tm_type u))
                                (#post0 #post1:R.term)
                                (d_0:RT.tot_typing g post0 
                                       (mk_arrow (ty, R.Q_Explicit) (elab_term tm_vprop)))
                                (d_1:RT.tot_typing g post1 
                                       (mk_arrow (ty, R.Q_Explicit) (elab_term tm_vprop)))
                                (#pf:_)
                                (eq:RT.tot_typing g pf (mk_arrow (ty, R.Q_Explicit) 
                                      (stt_vprop_equiv (app0 post0) (app0 post1))))
  : GTot ( pf: R.term &
           RT.tot_typing g pf (stt_vprop_post_equiv u ty post0 post1) )
  = admit()


let stt_vprop_post_equiv_is_prop (#g:R.env) (#ty:R.term) (#u:_)
                                 (d_ty:RT.tot_typing g ty (RT.tm_type u))
                                 (#post0 #post1:R.term)
                                 (d_0:RT.tot_typing g post0 
                                                (mk_arrow (ty, R.Q_Explicit) (elab_term tm_vprop)))
                                 (d_1:RT.tot_typing g post1 
                                                (mk_arrow (ty, R.Q_Explicit) (elab_term tm_vprop)))
  : GTot (RT.tot_typing g (stt_vprop_post_equiv u ty post0 post1) RT.tm_prop)
  = admit()

let inst_sub_stt (#g:R.env) (#u:_) (#a #pre1 #pre2 #post1 #post2 #r:R.term)
                 (d_a: RT.tot_typing g a (RT.tm_type u))
                 (d_pre1: RT.tot_typing g pre1 (elab_term tm_vprop))
                 (d_pre2: RT.tot_typing g pre2 (elab_term tm_vprop))
                 (d_post1:RT.tot_typing g post1 (mk_arrow (a, R.Q_Explicit) (elab_term tm_vprop)))
                 (d_post2:RT.tot_typing g post2 (mk_arrow (a, R.Q_Explicit) (elab_term tm_vprop)))
                 (pre_equiv:RT.tot_typing g (`()) (stt_vprop_equiv pre1 pre2))
                 (post_equiv:RT.tot_typing g (`()) (stt_vprop_post_equiv u a post1 post2))
                 (d_r:RT.tot_typing g r (mk_stt_comp u a pre1 post1))
  : GTot (RT.tot_typing g (mk_sub_stt u a pre1 pre2 post1 post2 r) (mk_stt_comp u a pre2 post2))
  = admit()

let vprop_arrow (t:term) : term = tm_arrow (null_binder t) None (C_Tot tm_vprop)

#push-options "--fuel 2 --ifuel 1 --z3rlimit_factor 4 --query_stats"
let st_equiv_soundness (g:stt_env)
                       (c0 c1:ln_comp) 
                       (d:st_equiv g c0 c1)
                       (r:R.term)
                       (d_r:RT.tot_typing (elab_env g) r (elab_comp c0)) 
  : GTot (RT.tot_typing (elab_env g) (elab_sub c0 c1 r) (elab_comp c1))
  = if C_ST? c0 && C_ST? c1 then
      let ST_VPropEquiv _ _ _ x pre_typing res_typing post_typing eq_pre eq_post = d in
      // assert (None? (lookup_ty g x));
      assert (None? (lookup g x));
      assume (~(x `Set.mem` RT.freevars (elab_term (comp_post c0))));
      assume (~(x `Set.mem` RT.freevars (elab_term (comp_post c1))));      
      let open_term_spec (e:R.term) (x:var)
          : Lemma 
            (RT.open_term e x == RT.subst_term e (RT.open_with_var x 0))
            [SMTPat (RT.open_term e x)]
          = RT.open_term_spec e x
      in
      let pre_equiv = VPropEquiv.vprop_equiv_unit_soundness pre_typing eq_pre in
      let g' = push_binding g x ppname_default (comp_res c0) in
      elab_open_commute (comp_post c0) x;
      elab_open_commute (comp_post c1) x;      
      let post_equiv
        : RT.tot_typing (RT.extend_env (elab_env g) x (elab_term (comp_res c0)))
                    (`())
                    (stt_vprop_equiv 
                      (RT.open_term (elab_term (comp_post c0)) x)
                      (RT.open_term (elab_term (comp_post c1)) x))
          = VPropEquiv.vprop_equiv_unit_soundness post_typing eq_post
      in
      let t0 = elab_term (comp_res c0)  in
      let r_res_typing = tot_typing_soundness res_typing in
      RT.close_open_inverse (elab_term (comp_post c0)) x;
      RT.close_open_inverse (elab_term (comp_post c1)) x;
      let d 
        : RT.tot_typing (elab_env g) _ 
                    (mk_arrow (t0, R.Q_Explicit)
                              (stt_vprop_equiv (elab_term (comp_post c0))
                                              (elab_term (comp_post c1))))
          = assume (stt_vprop_equiv (elab_term (comp_post c0))
                                    (elab_term (comp_post c1)) ==
                    RT.subst_term
                      (stt_vprop_equiv
                        (RT.open_term (elab_term (comp_post c0)) x)
                        (RT.open_term (elab_term (comp_post c1)) x))
                      [ RT.ND x 0 ]);
            RT.T_Abs _ _ _ (`()) _ (comp_u c1) _ R.Q_Explicit _ r_res_typing post_equiv
      in
      let d = stt_vprop_equiv_abstract d in
      let abs_post0_typing
        : RT.tot_typing (elab_env g)
                        (elab_comp_post c0) // mk_abs t0 (elab_pure (comp_post c0)))
                        (elab_term (vprop_arrow (comp_res c0)))
        = mk_t_abs_tot _ _ res_typing post_typing
      in
      let abs_post1_typing
        : RT.tot_typing (elab_env g)
                        (elab_comp_post c1) //mk_abs t0 (elab_pure (comp_post c1)))
                        (elab_term (vprop_arrow (comp_res c0)))
        = mk_t_abs_tot _ _ res_typing (fst (vprop_equiv_typing eq_post) post_typing)
      in
      let (| pf, d |) =
        inst_intro_vprop_post_equiv r_res_typing abs_post0_typing abs_post1_typing d in
      let post_equiv =
        RT.T_PropIrrelevance _ _ _ _ _ d
          (RT.T_Sub _ _ _ _
            (stt_vprop_post_equiv_is_prop r_res_typing abs_post0_typing abs_post1_typing)
            (RT.Relc_total_ghost _ _))
      in
      inst_sub_stt #_ #(comp_u c1) r_res_typing 
                  (tot_typing_soundness pre_typing)
                  (tot_typing_soundness (fst (vprop_equiv_typing eq_pre) pre_typing))
                  abs_post0_typing
                  abs_post1_typing
                  pre_equiv
                  post_equiv
                  d_r
    else admit ()
#pop-options
