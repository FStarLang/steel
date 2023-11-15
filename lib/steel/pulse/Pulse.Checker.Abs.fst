module Pulse.Checker.Abs

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base

module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RU = Pulse.RuntimeUtils
(* Infers the the type of the binders from the specification alone, not the body *)

let range_of_st_comp (st:st_comp) =
  RU.union_ranges (st.pre.range) (st.post.range)

let range_of_comp (c:comp) =
  match c with
  | C_Tot t -> t.range
  | C_ST st -> range_of_st_comp st
  | C_STAtomic _ st -> range_of_st_comp st
  | C_STGhost _ st -> range_of_st_comp st

let rec arrow_of_abs (t:st_term { Tm_Abs? t.term })
  : T.Tac term
  = let Tm_Abs { b; q; ascription; body } = t.term in
    if Tm_Abs? body.term
    then (
      let arr = arrow_of_abs body in
      { tm_arrow b q (C_Tot arr) with range = RU.union_ranges b.binder_ty.range arr.range }
    )
    else (
      { tm_arrow b q ascription with range = RU.union_ranges b.binder_ty.range (range_of_comp ascription) }
    )
module Env = Pulse.Typing.Env

let rec rebuild_abs (g:env) (t:st_term) (annot:T.term)
  : T.Tac (t:st_term { Tm_Abs? t.term })
  = match t.term, R.inspect_ln annot with
    | Tm_Abs { b; q; ascription=C_Tot un; body }, R.Tv_Arrow b' c' -> (
      let ty = readback_ty (T.inspect_binder b').sort in
      let comp = R.inspect_comp c' in
      match ty, comp with
      | Some ty, T.C_Total res_ty ->
        let b = { binder_ty = ty ; binder_ppname = b.binder_ppname } in
        let body = rebuild_abs g body res_ty in
        { t with term = Tm_Abs { b; q; ascription=C_Tot un; body }}
      | _ ->
        Env.fail g (Some t.range) 
            (Printf.sprintf "Unexpected type of abstraction: %s"
                (T.term_to_string annot))
    )
    | Tm_Abs { b; q; ascription=_; body }, R.Tv_Arrow b' c' -> (
      let ty = readback_ty (T.inspect_binder b').sort in
      let comp = R.inspect_comp c' in
      match ty, comp with
      | Some ty, R.C_Total res -> (
        let c = readback_comp res in
        match c with
        | None -> 
          Env.fail g (Some t.range) 
                      (Printf.sprintf "Unexpected computation type in abstraction: %s"
                          (T.term_to_string res))
        | Some c ->
          let b = { binder_ty = ty ; binder_ppname = b.binder_ppname } in
          { t with term = Tm_Abs { b; q; ascription=c; body }}
      )
      | _ ->
        Env.fail g (Some t.range) 
                    (Printf.sprintf "Unexpected type of abstraction: %s"
                          (T.term_to_string annot))
    )
    | _ -> 
      Env.fail g (Some t.range) 
                (Printf.sprintf "Unexpected arity of abstraction: expected a term of type %s"
                      (T.term_to_string annot))

let preprocess_abs
      (g:env)
      (t:st_term{Tm_Abs? t.term})
  : T.Tac (t:st_term { Tm_Abs? t.term })
  = let annot = arrow_of_abs t in
    let annot, _ = Pulse.Checker.Pure.instantiate_term_implicits g annot in
    match annot.t with
    | Tm_FStar annot ->
      rebuild_abs g t annot
    | _ ->
      Env.fail g (Some t.range) 
                 (Printf.sprintf "Expected an arrow type as an annotation, got %s"
                          (P.term_to_string annot))

let check_effect_annotation g r (c_annot c_computed:comp) =
  match c_annot, c_computed with
  | C_Tot _, C_Tot _ -> ()
  | C_ST _, C_ST _ -> ()
  | C_STAtomic i c1, C_STAtomic j c2
  | C_STGhost i c1, C_STGhost j c2 ->
    if eq_tm i j then () else

    let b = mk_binder "res" Range.range_0 c2.res in
    let phi =
      // mk_forall c1.u c1.res
       mk_sq_eq2 u_zero tm_inames i j
                      //  (tm_pureabs (Sealed.seal "res") c1.res None i)
                      //  (tm_pureabs (Sealed.seal "res") c2.res None j)
    in
    info g (Some r) ("Checking " ^ P.term_to_string phi);
    let (| phi, typing |) = check_term_with_expected_type_and_effect g phi T.E_Total tm_prop in
    let ok = T.with_policy T.SMTSync (fun () -> try_check_prop_validity g phi typing) in
    if Some? ok then () else
      let open Pulse.PP in
      fail_doc g (Some i.range) [
        text "Annotated effect expects only invariants in" ^/^
          pp i ^/^
        text "to be opened; but computed effect claims that invariants" ^/^
          pp j ^/^
        text "are opened"]
  | _, _ ->
    fail g (Some r)
           (Printf.sprintf "Expected effect %s but this function body has effect %s"
                  (P.tag_of_comp c_annot)
                  (P.tag_of_comp c_computed))


#push-options "--z3rlimit_factor 2 --fuel 0 --ifuel 1"
let rec check_abs_core
  (g:env)
  (t:st_term{Tm_Abs? t.term})
  (check:check_t)
  : T.Tac (t:st_term & c:comp & st_typing g t c) =
  let range = t.range in
  match t.term with  
  | Tm_Abs { b = {binder_ty=t;binder_ppname=ppname}; q=qual; ascription=c; body } -> //pre=pre_hint; body; ret_ty; post=post_hint_body } ->

    (*  (fun (x:t) -> {pre_hint} body : t { post_hint } *)
    let (| t, _, _ |) = check_tot_term g t in //elaborate it first
    let (| u, t_typing |) = check_universe g t in //then check that its universe ... We could collapse the two calls
    let x = fresh g in
    let px = ppname, x in
    let var = tm_var {nm_ppname=ppname;nm_index=x} in
    let g' = push_binding g x ppname t in
    let body_opened = open_st_term_nv body px in
    match body_opened.term with
    | Tm_Abs _ ->
      let (| body, c_body, body_typing |) = check_abs_core g' body_opened check in
      check_effect_annotation g' body.range c c_body;
      FV.st_typing_freevars body_typing;
      let body_closed = close_st_term body x in
      assume (open_st_term body_closed x == body);
      let b = {binder_ty=t;binder_ppname=ppname} in
      let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
      let tres = tm_arrow {binder_ty=t;binder_ppname=ppname} qual (close_comp c_body x) in
      (| _, C_Tot tres, tt |)
    | _ ->
      let pre_opened, inames_opened, ret_ty, post_hint_body = 
        match c with
        | C_Tot _ ->
          fail g (Some body.range)
            "Unexpected error: found a total computation annotation on a top-level function" 

        | _ -> 
          open_term_nv (comp_pre c) px,
          (if C_ST? c then tm_emp_inames else open_term_nv (comp_inames c) px),
          Some (open_term_nv (comp_res c) px),
          Some (open_term' (comp_post c) var 1)
      in
      let (| pre_opened, pre_typing |) = check_vprop g' pre_opened in
      let pre = close_term pre_opened x in
      let post : post_hint_opt g' =
        match post_hint_body with
        | None ->
          let open Pulse.PP in
          fail_doc g (Some body.range) [text "Top-level functions must be annotated with pre and post conditions"]
        | Some post ->
          let post_hint_typing
            : post_hint_t
            = Pulse.Checker.Base.intro_post_hint (push_context "post_hint_typing" range g') (Some (ctag_of_comp_st c)) ret_ty post
          in
          Some post_hint_typing
      in

      let ppname = mk_ppname_no_range "_fret" in
      let r  = check g' pre_opened pre_typing post ppname body_opened  in
      let (| body, c_body, body_typing |) : st_typing_in_ctxt g' pre_opened post =
        apply_checker_result_k #_ #_ #(Some?.v post) r ppname in

      let c'' = match c with
      | C_ST _ -> c
      | C_STGhost inames c_st -> C_STGhost inames_opened c_st
      | C_STAtomic inames c_st -> C_STGhost inames_opened c_st
      in

      check_effect_annotation g' body.range c'' c_body;

      (* HACK: preserve invariants *)
      let old_c_body = c_body in
      let c_body = match c_body, c with
      | C_STGhost _ c_st, C_STGhost inames _ -> C_STGhost inames c_st
      | C_STAtomic _ c_st, C_STAtomic inames _ -> C_STAtomic inames c_st
      | _ -> c_body
      in
      assume (old_c_body == c_body);

      FV.st_typing_freevars body_typing;
      let body_closed = close_st_term body x in
      assume (open_st_term body_closed x == body);
      let b = {binder_ty=t;binder_ppname=ppname} in
      let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
      let tres = tm_arrow {binder_ty=t;binder_ppname=ppname} qual (close_comp c_body x) in

      let open Pulse.PP in
      warn_doc g (Some body.range) [
        text "Returning type" ^/^ pp tres;
        text "c_body = " ^/^ pp (c_body <: comp);
        text "original asc = " ^/^ pp c;
      ];

      (| _, C_Tot tres, tt |)

let check_abs (g:env) (t:st_term{Tm_Abs? t.term}) (check:check_t)
  : T.Tac (t:st_term & c:comp & st_typing g t c) =
  let t = preprocess_abs g t in
  check_abs_core g t check
