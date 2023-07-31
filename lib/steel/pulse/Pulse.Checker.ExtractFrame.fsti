module Pulse.Checker.ExtractFrame

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common

// Simple wrapper around check_frameable
val remove_from_vprop (#g: env) (#ctxt: term)
  (to_remove: term) (ctxt_typing: tot_typing g ctxt tm_vprop):
  T.Tac (res:term & tot_typing g res tm_vprop & vprop_equiv g (tm_star to_remove res) ctxt)

// computes a frame that works for the whole typing derivation
val compute_frame (#g: env) (#t: st_term) (#c: comp)
  (ty: st_typing g t c)
: T.Tac (frame: vprop & tot_typing g frame tm_vprop)

// removes a frame from a typing derivation
// this frame must be included in all non-trivial frame applications
// in the typing derivation
val extract_frame (#g: env) (#t: st_term) (#c: comp) (#frame: vprop)
  (typing_frame: tot_typing g frame tm_vprop) (ty: st_typing g t c)
: T.Tac (c':comp & st_typing g t c' & vprop)

// composes compute_frame with extract_frame
val compute_and_extract_frame (#g: env) (#t: st_term) (#c: comp)
  (ty: st_typing g t c)
: T.Tac (frame:vprop & tot_typing g frame tm_vprop & c': comp & st_typing g t c')

val infer_frame_and_typecheck (#g: env) (#ctxt: term)
  (allow_inst: bool)
  (t: st_term)
  (ctxt_typing: tot_typing g ctxt tm_vprop)
  (post_hint: post_hint_opt g)
  (check':bool -> check_t)
  (modify_type_derivation: bool)
: T.Tac (
  t: st_term &
  c:comp{(stateful_comp c /\ ~modify_type_derivation) ==> comp_post_matches_hint c post_hint} &
  frame:vprop &
  tot_typing g frame tm_vprop &
  (st_typing g t c &
  (squash (stateful_comp c /\ ~modify_type_derivation) -> vprop_equiv g (tm_star frame (comp_pre c)) ctxt))
 )