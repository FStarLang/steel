module Pulse.Checker.Framing
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.VPropEquiv
module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.V2.Builtins
module FV = Pulse.Typing.FV
module Metatheory = Pulse.Typing.Metatheory
module VP = Pulse.Checker.VPropEquiv

let print_vprop_l (vps:list term) : T.Tac string =
  Printf.sprintf "[%s]"
    (String.concat ";\n " (T.map P.term_to_string vps))

let print_framing_failure ff = 
  Printf.sprintf " { unmatched_preconditions = %s;\n remaining_context = %s\n}"
    (print_vprop_l ff.unmatched_preconditions)
    (print_vprop_l ff.remaining_context)


let equational (t:term) : bool =
  match t.t with
  | Tm_FStar host_term ->
    (match R.inspect_ln host_term with
     | R.Tv_Match _ _ _ -> true
     | _ -> false)
  | _ -> false

#push-options "--z3rlimit_factor 4"
let check_one_vprop g (p q:term) : T.Tac (option (vprop_equiv g p q)) =
  if eq_tm p q
  then Some (VE_Refl _ _)
  else
    // let _ = T.print ("Framing.check_one_vprop: checking extensional equality\n") in
    let check_extensional_equality =
      match is_pure_app p, is_pure_app q with
      | Some (hd_p, _, _), Some (hd_q, _, _) -> eq_tm hd_p hd_q
      | _, _ -> equational p || equational q
    in
    if check_extensional_equality
    then
      let v0 = elab_term p in
      let v1 = elab_term q in
      match T.check_equiv (elab_env g) v0 v1 with
      | Some token, _ -> Some (VE_Ext g p q token)
      | None, _ -> None
    else None
#pop-options

type split_one_vprop_res g (p:term) (qs:list term) =
  r:option (l:list term & q:term & vprop_equiv g p q & list term){
    Some? r ==>
    (let Some (| l, q, _, r |) = r in
     qs == (l @ [q]) @ r)
  }

let rec maybe_split_one_vprop g (p:term) (qs:list term)
  : T.Tac (split_one_vprop_res g p qs)
  = match qs with
    | [] -> None
    | q::qs ->
      let d_opt = check_one_vprop g p q in
      if Some? d_opt
      then Some (| [], q, Some?.v d_opt, qs |)
      else match maybe_split_one_vprop g p qs with
           | None -> None
           | Some (| l, q', d, r |) -> Some (| q::l, q', d, r |)

let framing_success g req ctxt =
  (frame:list term &
   vprop_equiv g (VP.list_as_vprop (req @ frame)) (VP.list_as_vprop ctxt))
   
let try_frame_result g req ctxt = either (framing_success g req ctxt) framing_failure

let mk_framing_failure #g #req #req' #ctxt #ctxt'
                       (unmatched_pre:term)
                       (res:try_frame_result g req ctxt)
  : try_frame_result g req' ctxt'
  = match res with
    | Inr failure -> 
      Inr { failure with
            unmatched_preconditions=
              unmatched_pre::failure.unmatched_preconditions
          }
    | Inl (| frame, _ |) ->  
      Inr { unmatched_preconditions = [unmatched_pre];
            remaining_context = frame }
            
let rec try_split_vprop g (req:list term) (ctxt:list term)
  : T.Tac 
    (either (frame:list term &
             vprop_equiv g (VP.list_as_vprop (req @ frame)) (VP.list_as_vprop ctxt))
            framing_failure)
  = match req with
    | [] -> Inl (| ctxt, VE_Refl g _ |)
    | hd::tl ->
      match maybe_split_one_vprop g hd ctxt with
      | None ->
        mk_framing_failure hd (try_split_vprop g tl ctxt)

      | Some (| l, q, d, r |) -> 
        let d1
          : vprop_equiv g (VP.list_as_vprop ctxt)
                          (VP.list_as_vprop (hd :: (l@r)))
          = VP.vprop_equiv_swap_equiv g l r hd q d
        in
        match try_split_vprop g tl (l @ r) with
        | Inr failure -> Inr failure
        | Inl (| frame, d |) ->
          let d
            : vprop_equiv g (VP.list_as_vprop (tl @ frame))
                            (VP.list_as_vprop (l @ r))
            = d
          in
          let dd
            : vprop_equiv g (VP.list_as_vprop ((hd::tl) @ frame))
                            (VP.list_as_vprop (hd :: (l @ r)))
            = VP.list_as_vprop_ctx g [hd] [hd] _ _ (VE_Refl _ _) d
          in
          let ddd = VE_Trans _ _ _ _ dd (VE_Sym _ _ _ d1) in
          Inl (| frame, ddd |)


let split_vprop (g:env)
                (ctxt:term)
                (ctxt_typing: tot_typing g ctxt tm_vprop)
                (req:term)
   : T.Tac (either (frame:term &
                    tot_typing g frame tm_vprop &
                    vprop_equiv g (tm_star req frame) ctxt)
                   framing_failure)
   = let ctxt_l = VP.vprop_as_list ctxt in
     let req_l = VP.vprop_as_list req in
     match try_split_vprop g req_l ctxt_l with
     | Inr failure -> 
       Inr failure 
     | Inl (| frame, veq |) ->
       let d = VP.vprop_equiv_split_frame g ctxt req frame veq in
       let typing : tot_typing g (VP.list_as_vprop frame) tm_vprop = 
         let fwd, bk = VP.vprop_equiv_typing d in
         let star_typing = bk ctxt_typing in
         star_typing_inversion_r star_typing
       in
       Inl (| VP.list_as_vprop frame, typing, d |)



let rec all_matches g p q
  : T.Tac (match_result g p q)
  = match p with
    | [] ->
      { matched = []; unmatched_p = p; unmatched_q = q; p_eq = VE_Refl _ _; q_eq = VE_Refl _ _ }
    
    | hd::tl ->
      match maybe_split_one_vprop g hd q with
      | None -> //hd is in unmatched_p
        let res = all_matches g tl q in
        let p_eq : vprop_equiv g (list_as_vprop p) (list_as_vprop (hd::res.unmatched_p @ res.matched)) = 
          VP.list_as_vprop_ctx _ [hd] [hd] _ _ (VE_Refl _ _) res.p_eq in
        { res with unmatched_p = hd::res.unmatched_p; p_eq}

      | Some res ->
        let (| l, found, v, r |) = res in
        assert (q == (l @ [found]) @ r);
        let v : vprop_equiv g hd found = v in
        let res = all_matches g tl (l @ r) in
        let aux hd tl l r (v:vprop_equiv g (list_as_vprop tl) (list_as_vprop (l @ r)))
          : vprop_equiv g (list_as_vprop (hd::tl)) (list_as_vprop (l @ (hd::r)))
          = let v =  
                VE_Trans _ _ _ _ (VP.list_as_vprop_ctx _ [hd] [hd] _ _ (VE_Refl _ _) v)
                                 (VE_Sym _ _ _ (VP.vprop_equiv_swap_equiv _ _ _ hd hd (VE_Refl _ _)))
            in
            (VE_Trans _ _ _ _ v (VE_Sym _ _ _ (VP.list_as_vprop_assoc _ _ _ _)))
        in
        let q_eq : vprop_equiv g (list_as_vprop q) (list_as_vprop (res.unmatched_q @ (hd::res.matched))) = 
           let q_eq' : vprop_equiv g (list_as_vprop q) (list_as_vprop (hd::(l@r))) =
                (VP.vprop_equiv_swap_equiv _ l r hd found v)
           in
           VE_Trans _ _ _ _ q_eq' (aux hd (l@r) _ _ res.q_eq)
        in
        { res with matched = hd::res.matched;
                   p_eq = aux hd tl _ _ res.p_eq;
                   q_eq }


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

#push-options "--z3rlimit_factor 2"
let check_vprop_equiv
  (g:env)
  (vp1 vp2:term)
  (vp1_typing:tot_typing g vp1 tm_vprop)

  : T.Tac (vprop_equiv g vp1 vp2) =

  match split_vprop g vp1 vp1_typing vp2 with
  | Inr failure ->
    fail g None (Printf.sprintf
              "check_vprop_equiv: %s and %s are not equivalent; missing preconditions:\n%s\n"
                (P.term_to_string vp1)
                (P.term_to_string vp2)
                (String.concat "\n" (T.map P.term_to_string failure.unmatched_preconditions)))
                
  | Inl (| frame, _, d |) ->
    match check_equiv_emp g frame with
    | Some d_frame_equiv_emp ->
      let d : vprop_equiv g (tm_star vp2 frame) vp1 = d in
      let d : vprop_equiv g vp1 (tm_star vp2 frame) =
        VE_Sym _ _ _ d in
      let d' : vprop_equiv g (tm_star vp2 frame) (tm_star vp2 tm_emp) =
        VE_Ctxt _ _ _ _ _ (VE_Refl _ vp2) d_frame_equiv_emp in
      let d : vprop_equiv g vp1 (tm_star vp2 tm_emp) =
        VE_Trans _ _ _ _ d d' in
      let d' : vprop_equiv g (tm_star vp2 tm_emp) (tm_star tm_emp vp2) = VE_Comm _ _ _ in
      let d  : vprop_equiv g vp1 (tm_star tm_emp vp2) = VE_Trans _ _ _ _ d d' in
      let d' : vprop_equiv g (tm_star tm_emp vp2) vp2 = VE_Unit _ _ in
      VE_Trans _ _ _ _ d d'
    | None ->
      fail g None (Printf.sprintf "check_vprop_equiv: %s and %s are not equivalent, frame: %s\n"
                             (P.term_to_string vp1)
                             (P.term_to_string vp2)
                             (P.term_to_string frame))
#pop-options

let freevars_comp_post (c:comp { stateful_comp c })
  : Lemma (freevars (comp_post c) `Set.subset` freevars_comp c)
  = ()

#push-options "--z3rlimit_factor 20 --query_stats --fuel 4 --ifuel 2 --query_stats"

  
let check_frameable (#g:env)
                    (#ctxt:term)
                    (ctxt_typing: tot_typing g ctxt tm_vprop)
                    (req:term)
   : T.Tac (either (frame_for_req_in_ctxt g ctxt req)
                   framing_failure)
   = split_vprop g ctxt ctxt_typing req

let apply_frame (#g:env)
                (#t:st_term)
                (#ctxt:term)
                (ctxt_typing: tot_typing g ctxt tm_vprop)
                (#c:comp { stateful_comp c })
                (t_typing: st_typing g t c)
                (frame_t:frame_for_req_in_ctxt g ctxt (comp_pre c))
  : Tot (c':comp_st { comp_pre c' == ctxt /\
                      comp_res c' == comp_res c /\
                      comp_u c' == comp_u c /\
                      comp_post c' == tm_star (comp_post c) (frame_of frame_t) } &
           st_typing g t c')
  = let s = st_comp_of_comp c in
    let (| frame, frame_typing, ve |) = frame_t in
    let t_typing
      : st_typing g t (add_frame c frame)
      = T_Frame g t c frame frame_typing t_typing in
    let c' = add_frame c frame in
    let c'_typing = Metatheory.st_typing_correctness t_typing in
    let s' = st_comp_of_comp c' in
    let ve: vprop_equiv g s'.pre ctxt = ve in
    let s'' = { s' with pre = ctxt } in
    let c'' = c' `with_st_comp` s'' in
    assert (comp_post c' == comp_post c'');
    let ve: vprop_equiv g (comp_pre c') (comp_pre c'') = ve in    
    let st_typing = Metatheory.comp_typing_inversion c'_typing in
    let (| res_typing, pre_typing, x, post_typing |) = Metatheory.st_comp_typing_inversion st_typing in
    let st_equiv = ST_VPropEquiv g c' c'' x pre_typing res_typing post_typing ve (VE_Refl _ _) in
    let t_typing = T_Equiv _ _ _ _ t_typing st_equiv in
    (| c'', t_typing |)


let try_frame_pre (#g:env)
                  (#t:st_term)
                  (#pre:term)
                  (pre_typing: tot_typing g pre tm_vprop)
                  (#c:comp { stateful_comp c })
                  (t_typing: st_typing g t c)
  : T.Tac (either (c':comp_st { comp_pre c' == pre } &
                   st_typing g t c')
                  framing_failure)
  = match check_frameable pre_typing (comp_pre c) with
    | Inr failure -> Inr failure  
    | Inl frame_t -> 
      let (| c', st_d |) = apply_frame pre_typing t_typing frame_t in
      Inl (| c', st_d |)
  
let frame_empty (#g:env)
                (#pre:term)
                (pre_typing: tot_typing g pre tm_vprop)
                (#u:universe)
                (#ty:term) 
                (ut:universe_of g ty u)
                (t:st_term)
                (c0:comp_st{ comp_pre c0 == tm_emp })
                (d:st_typing g t c0)
  : T.Tac (c:comp_st { comp_pre c == pre} &
           st_typing g t c)
  = let d = T_Frame g t c0 pre pre_typing d in
    let c = add_frame c0 pre in
    let s = st_comp_of_comp c in
    let d : st_typing g t c = d in
    let s' = { s with pre = pre } in
    let c' = c `with_st_comp` s' in
    assert (stateful_comp c');
    let c_typing = Metatheory.st_typing_correctness d in
    let st_typing = Metatheory.comp_typing_inversion c_typing in
    let (| res_typing, pre_typing, x, post_typing |) = Metatheory.st_comp_typing_inversion st_typing in 
    let eq
      : st_equiv g c c'
      = ST_VPropEquiv g c c' x
                        pre_typing
                        res_typing
                        post_typing
                        (VE_Unit g pre)
                        (VE_Refl _ _)
    in
    (| c', T_Equiv _ _ _ _ d eq |)
#pop-options
