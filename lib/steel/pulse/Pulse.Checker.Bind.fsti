module Pulse.Checker.Bind
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Checker.Common

let st_comp_with_pre (st:st_comp) (pre:term) : st_comp = { st with pre }

val mk_bind (g:env)
            (pre:term)
            (e1:st_term)
            (e2:st_term)
            (c1:comp_st)
            (c2:comp_st)
            (px:nvar)
            (d_e1:st_typing g e1 c1)
            (d_c1res:tot_typing g (comp_res c1) (tm_type (comp_u c1)))
            (d_e2:st_typing (extend (snd px) (Inl (comp_res c1)) g) (open_st_term_nv e2 px) c2)
            (res_typing:universe_of g (comp_res c2) (comp_u c2))
            (post_typing:tot_typing (extend (snd px) (Inl (comp_res c2)) g) (open_term_nv (comp_post c2) px) Tm_VProp)
  : T.TacH (t:st_term &
            c:comp_st { st_comp_of_comp c == st_comp_with_pre (st_comp_of_comp c2) pre } &
            st_typing g t c)
           (requires fun _ ->
              let _, x = px in
              comp_pre c1 == pre /\
              None? (lookup g x) /\
              (~(x `Set.mem` freevars_st e2)) /\
              open_term (comp_post c1) x == comp_pre c2 /\
              (~ (x `Set.mem` freevars (comp_post c2))))
           (ensures fun _ _ -> True)

val bind_res_and_post_typing (g:env) (s2:st_comp)
                             (x:var { Pulse.Typing.Metatheory.fresh_wrt x g (freevars s2.post) })
                             (post_hint:post_hint_opt g { comp_post_matches_hint (C_ST s2) post_hint })
  : T.Tac (universe_of g s2.res s2.u &
           tot_typing (extend x (Inl s2.res) g) (open_term_nv s2.post (v_as_nv x)) Tm_VProp)

val check_bind (g:env)
               (t:st_term{Tm_Bind? t.term})
               (pre:term)
               (pre_typing:tot_typing g pre Tm_VProp)
               (post_hint:post_hint_opt g)               
               (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)

val check_tot_bind
  (g:env)
  (t:st_term{Tm_TotBind? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)