module Pulse.Prover.ElimExists

open Pulse.Syntax
open Pulse.Typing

module T = FStar.Tactics.V2

open Pulse.Checker.VPropEquiv

open Pulse.Prover.Common

let should_elim_exists (v:vprop) : T.Tac bool =
  match v.t with
  | Tm_ExistsSL _ _ _ -> true
  | _ -> false

let mk (#g:env) (#v:vprop) (v_typing:tot_typing g v tm_vprop)
  : T.Tac (option (x:ppname &
                   t:st_term &
                   c:comp { stateful_comp c /\ comp_pre c == v } &
                   st_typing g t c)) =

  match v.t with
  | Tm_ExistsSL u { binder_ppname=nm; binder_ty = t } p ->
    let x = fresh g in
    let c = Pulse.Typing.comp_elim_exists u t p (nm, x) in
    let tm_typing : st_typing g _ c =
        T_ElimExists g (comp_u c) t p x (magic()) (magic())
    in
    Some (| nm, _, c, tm_typing |)
  | _ -> None

let elim_exists_frame (#g:env) (#ctxt #frame:vprop)
  (ctxt_frame_typing:tot_typing g (ctxt * frame) tm_vprop)
  (uvs:env { disjoint uvs g })
  : T.Tac (g':env { env_extends g' g /\ disjoint uvs g' } &
           ctxt':term &
           tot_typing g' (ctxt' * frame) tm_vprop &
           continuation_elaborator g (ctxt * frame) g' (ctxt' * frame)) =
  add_elims should_elim_exists mk ctxt_frame_typing uvs

let elim_exists (#g:env) (#ctxt:term)
  (ctxt_typing:tot_typing g ctxt tm_vprop)
  : T.Tac (g':env { env_extends g' g } &
           ctxt':term &
           tot_typing g' ctxt' tm_vprop &
           continuation_elaborator g ctxt g' ctxt') =

  let ctxt_emp_typing : tot_typing g (tm_star ctxt tm_emp) tm_vprop = magic () in
  let (| g', ctxt', ctxt'_emp_typing, k |) =
    elim_exists_frame ctxt_emp_typing (mk_env (fstar_env g)) in
  let k = k_elab_equiv k (VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _))
                         (VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _)) in
  (| g', ctxt', star_typing_inversion_l ctxt'_emp_typing, k |)

let elim_exists_pst (#preamble:_) (pst:prover_state preamble)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst /\
                                        pst'.unsolved == pst.unsolved }) =

  let (| g', remaining_ctxt', ty, k |) =
    elim_exists_frame
      #pst.pg
      #(list_as_vprop pst.remaining_ctxt)
      #(preamble.frame * pst.ss.(pst.solved))
      (magic ())
      pst.uvs in

  let k
    : continuation_elaborator
        pst.pg (list_as_vprop pst.remaining_ctxt * (preamble.frame * pst.ss.(pst.solved)))
        g' (remaining_ctxt' * (preamble.frame * pst.ss.(pst.solved))) = k in
  
  // some *s
  let k
    : continuation_elaborator
        pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved))
        g' ((remaining_ctxt' * preamble.frame) * pst.ss.(pst.solved)) =
    
    k_elab_equiv k (magic ()) (magic ()) in

  let k_new
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        g' ((remaining_ctxt' * preamble.frame) * pst.ss.(pst.solved)) =
    k_elab_trans pst.k k in
  
  assume (list_as_vprop (vprop_as_list remaining_ctxt') == remaining_ctxt');

  { pst with
    pg = g';
    remaining_ctxt = vprop_as_list remaining_ctxt';
    remaining_ctxt_frame_typing = magic ();
    k = k_new;
    goals_inv = magic ();  // weakening of pst.goals_inv
    solved_inv = ()
  }
