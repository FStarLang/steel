module Pulse.Prover.Common

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv

module T = FStar.Tactics.V2

module PS = Pulse.Prover.Substs

let vprop_typing (g:env) (t:term) = tot_typing g t tm_vprop

type continuation_elaborator
  (g:env) (ctxt:term)
  (g':env) (ctxt':term) =
  post_hint:post_hint_opt g ->
  checker_result_t g' ctxt' post_hint ->
  T.Tac (checker_result_t g ctxt post_hint)

val k_elab_unit (g:env) (ctxt:term)
  : continuation_elaborator g ctxt g ctxt

val k_elab_trans (#g0 #g1 #g2:env) (#ctxt0 #ctxt1 #ctxt2:term)
                 (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
                 (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2

val k_elab_equiv (#g1 #g2:env) (#ctxt1 #ctxt1' #ctxt2 #ctxt2':term)
                 (k:continuation_elaborator g1 ctxt1 g2 ctxt2)
                 (d1:vprop_equiv g1 ctxt1 ctxt1')
                 (d2:vprop_equiv g2 ctxt2 ctxt2')
  : continuation_elaborator g1 ctxt1' g2 ctxt2'

//
// A canonical continuation elaborator for Bind
//
val continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (tm_star ctxt (comp_pre c1)) tm_vprop)
  (x:var { None? (lookup g x) })
  : T.Tac (continuation_elaborator
             g                                (tm_star ctxt (comp_pre c1))
             (push_binding g x ppname_default (comp_res c1)) (tm_star (open_term (comp_post c1) x) ctxt))



//
// Scaffolding for adding elims
//
// Given a function f : vprop -> T.Tac bool that decides whether a vprop
//   should be elim-ed,
//   and an mk function to create the elim term, comp, and typing,
//   add_elims will create a continuation_elaborator
//

type mk_t =
  #g:env ->
  #v:vprop ->
  tot_typing g v tm_vprop ->
  T.Tac (option (x:ppname &
                 t:st_term &
                 c:comp { stateful_comp c /\ comp_pre c == v } &
                 st_typing g t c))

val add_elims (#g:env) (#ctxt:term) (#frame:term)
  (f:vprop -> T.Tac bool)
  (mk:mk_t)
  (ctxt_typing:tot_typing g (tm_star ctxt frame) tm_vprop)
  (uvs:env { disjoint uvs g })
   : T.Tac (g':env { env_extends g' g /\ disjoint uvs g' } &
            ctxt':term &
            tot_typing g' (tm_star ctxt' frame) tm_vprop &
            continuation_elaborator g (tm_star ctxt frame) g' (tm_star ctxt' frame))

noeq type preamble = {
  g0 : env;
  
  ctxt : vprop;
  frame : vprop;
  ctxt_frame_typing : vprop_typing g0 (tm_star ctxt frame);

  goals : vprop;
}

let op_Array_Access (ss:PS.ss_t) (t:term) =
  PS.ss_term t ss

let op_Star = tm_star

noeq type prover_state (preamble:preamble) = {
  pg : g:env { g `env_extends` preamble.g0 };

  remaining_ctxt : list vprop;
  remaining_ctxt_frame_typing : vprop_typing pg (list_as_vprop remaining_ctxt * preamble.frame);

  uvs : uvs:env { disjoint uvs pg };
  ss : PS.ss_t;

  solved : vprop;
  unsolved : list vprop;

  k : continuation_elaborator preamble.g0 (preamble.ctxt * preamble.frame)
                              pg ((list_as_vprop remaining_ctxt * preamble.frame) * ss.(solved));

  goals_inv : vprop_equiv (push_env pg uvs) preamble.goals (list_as_vprop unsolved * solved);
  solved_inv : squash (freevars ss.(solved) `Set.subset` dom pg);
}

let is_terminal (#preamble:_) (st:prover_state preamble) =
  st.unsolved == []

irreducible
let extend_post_hint_opt_g (g:env) (post_hint:post_hint_opt g) (g1:env { g1 `env_extends` g })
  : p:post_hint_opt g1 { p == post_hint } =
  match post_hint with
  | None -> None
  | Some post_hint ->
    assert (g `env_extends` post_hint.g);
    assert (g1 `env_extends` g);
    assert (g1 `env_extends` post_hint.g);
    Some post_hint

let st_typing_subst (g:env) (uvs:env { disjoint uvs g }) (t:st_term) (c:comp_st)
  (d:st_typing (push_env g uvs) t c)
  (ss:PS.ss_t)

  : T.Tac (option (st_typing g (PS.ss_st_term t ss) (PS.ss_comp c ss))) =

  let nts_opt = PS.ss_to_nt_substs g uvs ss in
  match nts_opt with
  | None -> None
  | Some nts ->
    let g' = mk_env (fstar_env g) in
    assert (equal (push_env uvs g') uvs);
    let d = PS.st_typing_nt_substs g uvs g' d nts in
    assume (equal (push_env g (PS.nt_subst_env g' nts)) g);
    Some d

let st_typing_weakening
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp) (d:st_typing (push_env g g') t c)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : st_typing (push_env g1 g') t c =

  let g2 = diff g1 g in
  let d = st_typing_weakening g g' t c d g2 in
  assert (equal (push_env (push_env g g2) g') (push_env g1 g'));
  d

let st_typing_weakening_end
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp) (d:st_typing (push_env g g') t c)
  (g'':env { g'' `env_extends` g' /\ disjoint g'' g })
  : st_typing (push_env g g'') t c = admit ()

let veq_weakening
  (g:env) (g':env { disjoint g g' })
  (#v1 #v2:vprop) (d:vprop_equiv (push_env g g') v1 v2)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : vprop_equiv (push_env g1 g') v1 v2 =

  let g2 = diff g1 g in
  let d = veq_weakening g g' d g2 in
  assert (equal (push_env (push_env g g2) g') (push_env g1 g'));
  d

let ss_extends (ss1 ss2:PS.ss_t) =
  Set.subset (PS.dom ss2) (PS.dom ss1) /\
  (forall (x:var). PS.contains ss2 x ==> PS.sel ss1 x == PS.sel ss2 x)

let pst_extends (#preamble:_) (pst1 pst2:prover_state preamble) =
  pst1.pg `env_extends` pst2.pg /\
  pst1.uvs `env_extends` pst2.uvs /\
  pst1.ss `ss_extends` pst2.ss

type prover_t =
  #preamble:_ ->
  pst1:prover_state preamble ->
  T.Tac (pst2:prover_state preamble { pst2 `pst_extends` pst1 /\
                                      is_terminal pst2 }) 
