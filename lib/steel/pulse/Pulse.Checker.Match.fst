module Pulse.Checker.Match

module T = FStar.Tactics.V2
module L = FStar.List.Tot.Base
module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common

let rec zipWith (f : 'a -> 'b -> T.Tac 'c) (l : list 'a) (m : list 'b) : T.Tac (list 'c) =
  match l, m with
  | [], [] -> []
  | x::xs, y::ys -> f x y :: zipWith f xs ys
  | _ -> T.fail "zipWith: length mismatch"

val tot_typing_weakening_n
   (#g:env) (#t:term) (#ty:term)
   (bs:list binding{all_fresh g bs})
   (d:tot_typing g t ty)
   : Tot (tot_typing (extend_env_bs g bs) t ty)
         (decreases bs)
let rec tot_typing_weakening_n bs d =
  match bs with
  | [] -> d
  | (x,t)::bs ->
    let d = Pulse.Typing.Metatheory.tot_typing_weakening x t d in
    tot_typing_weakening_n bs d

let samepat (b1 b2 : branch) : prop = fst b1 == fst b2
let samepats (bs1 bs2 : list branch) : prop = L.map fst bs1 == L.map fst bs2

let open_st_term_bs (t:st_term) (bs:list binding) : T.Tac st_term =
  let rec aux (bs:list binding) (i:nat) : subst =
    match bs with
    | [] -> []
    | b::bs ->
      (DT i (Pulse.Syntax.Pure.term_of_nvar (ppname_default, fst b))) :: aux bs (i+1)
  in
  let ss = aux (List.rev bs) 0 in
  subst_st_term t ss

val readback_binding : R.binding -> T.Tac binding
let readback_binding b =
  assume (host_term == R.term); // fixme! expose this fact
  match readback_ty b.sort with
  | Some sort -> (b.uniq, sort)
  | None ->
    let sort : term = {t=Tm_FStar b.sort; range=T.range_of_term b.sort} in
    (b.uniq, sort)

let rec map_opt f l = match l with
  | [] -> Some []
  | x::xs ->
    let? y = f x in
    let? ys = map_opt f xs in
    Some (y::ys)

let rec r_bindings_to_string (bs : list R.binding) : T.Tac string =
  match bs with
  | [] -> ""
  | b::bs ->
    (T.unseal b.ppname ^ "-" ^ string_of_int b.uniq ^ ":" ^ T.term_to_string b.sort ^ " ") ^ r_bindings_to_string bs

let rec bindings_to_string (bs : list binding) : T.Tac string =
  match bs with
  | [] -> ""
  | b::bs ->
    (string_of_int (fst b) ^ ":" ^ Pulse.Syntax.Printer.term_to_string (snd b) ^ " ") ^ bindings_to_string bs

let check_branch
        (g:env)
        (pre:term)
        (pre_typing: tot_typing g pre tm_vprop)
        (post_hint:post_hint_for_env g)
        (check:check_t)
        (p0:pattern)
        (e:st_term)
        (bs:list R.binding)
  : T.Tac (p:pattern{p == p0}
          & e:st_term
          & c:comp_st{comp_pre c == pre /\ comp_post_matches_hint c (Some post_hint)}
          & br_typing g p e c)
  =
  let bs = T.map readback_binding bs in
  assume (all_fresh g bs); // why??
  let g' = extend_env_bs g bs in
  let e = open_st_term_bs e bs in
  // TODO: extend with hyp
  let pre_typing = tot_typing_weakening_n bs pre_typing in
  let (| e, c, e_d |) = check g' e pre pre_typing (Some post_hint) in
  if not (stateful_comp c) then
    fail g (Some e.range) "Branch computation is not stateful";
  assert (all_fresh g bs);
  assume (bindings_for_pat_ok g p0 bs); // FIXME
  let br_d : br_typing g p0 e c = TBR g c p0 e bs e_d in
  (| p0, e, c, br_d |)


let check_branches
        (g:env)
        (pre:term)
        (pre_typing: tot_typing g pre tm_vprop)
        (post_hint:post_hint_for_env g)
        (check:check_t)
        (brs0:list branch)
        (bnds: list (list R.binding){L.length brs0 == L.length bnds})
  : T.Tac (brs:list branch{samepats brs0 brs}
           & c:comp_st{comp_pre c == pre /\ comp_post_matches_hint c (Some post_hint)}
           & brs_typing g brs c)
= if L.isEmpty brs0 then fail g None "empty match";
  let (p0, e0)::rest = brs0 in
  let bnds0::bnds = bnds in
  let (| p0, e0, c0, d0 |) = check_branch g pre pre_typing post_hint check p0 e0 bnds0 in
  let brs_d : (brs_d:list (br:branch & br_typing g (fst br) (snd br) c0){samepats brs0 (L.map dfst brs_d)}) =
    let tr1 (b:branch) (bs:list R.binding) : T.Tac (br:branch & br_typing g (fst br) (snd br) c0) =
      let (p, e) = b in
      let (| p, e, c, d |) = check_branch g pre pre_typing post_hint check p e bs in
      assume (c == c0); // FIXME: join and weaken
      (| (p,e), d |)
    in
    let r = zipWith tr1 rest bnds in
    assume (samepats (L.map dfst r) brs0);
    r
  in
  let brs = List.Tot.map dfst brs_d in
  let _ = List.Tot.Properties.append_l_nil brs in // odd
  let d : brs_typing g brs c0 =
    let rec aux (brs : list (br:branch & br_typing g (fst br) (snd br) c0))
               : brs_typing g (List.Tot.map dfst brs) c0
    =
      match brs with
      | [] -> TBRS_0 g c0
      | (|(p,e), d|)::rest ->
        TBRS_1 g c0 p e d (List.Tot.map dfst rest) (aux rest)
    in
    aux brs_d
  in
  (| brs, c0, d |)

let readback_pat_var (p : R.pattern & bool) : option (list (RT.pp_name_t & bool)) =
  match p with
  | R.Pat_Var st nm, i -> Some [(nm, i)]
  | R.Pat_Dot_Term _, _ -> Some []
  | _ -> None

let (let?) o f = 
  match o with
  | Some x -> f x
  | _ -> None

let rec lemma_map_len (f : 'a -> 'b) (xs : list 'a)
  : Lemma (L.length (L.map f xs) == L.length xs)
          [SMTPat (L.length (L.map f xs))]
  = match xs with
    | [] -> ()
    | x::xs -> lemma_map_len f xs

let rec lemma_map_index (f : 'a -> 'b) (xs : list 'a) (i : nat{i < L.length xs})
  : Lemma (L.map f xs `L.index` i == f (xs `L.index` i))
  = match i, xs with
    | 0, _ -> ()
    | _, x::xs -> lemma_map_index f xs (i-1)

let lemma_map_opt_lenx (f : 'a -> option 'b) (xs : list 'a)
  : Lemma (requires Some? (map_opt f xs))
          (ensures L.length xs == L.length (Some?.v (map_opt f xs)))
          [SMTPat (map_opt f xs)]
  = admit ()

let lemma_map_opt_index (f : 'a -> option 'b) (xs : list 'a) (ys : list 'b)
  : Lemma (requires map_opt f xs == Some ys)
          (ensures forall i. f (xs `L.index` i) == Some (ys `L.index` i))
  = admit ()

let readback_pat (p : R.pattern) : option pattern =
  match p with
  | R.Pat_Cons fv _ args ->
    let fv = R.inspect_fv fv in
    let? args = map_opt readback_pat_var args in
    let args = L.flatten args in
    Some (Pat_Cons {fv_name=fv; fv_range=Range.range_0} args)

  | R.Pat_Constant c ->
    Some (Pat_Constant c)

  | R.Pat_Var st nm ->
    Some (Pat_Var nm)

  | _ -> None

let elab_readback_pat (p : R.pattern)
  : Lemma (requires Some? (readback_pat p))
          (ensures elab_pat (Some?.v (readback_pat p)) == p)
  = match p with
  | R.Pat_Cons fv us_opt args ->
    admit()
    (* assert (R.pack_fv (R.inspect_fv fv) == fv); *)
    (* let Some rd_pat_vars = map_opt readback_pat_var args in *)
    (* let R.Pat_Cons fv' us_opt' args' = elab_pat (Some?.v (readback_pat p)) in *)
    (* lemma_map_opt_index readback_pat_var args rd_pat_vars; *)
    (* let aux1 (i:nat{i < L.length args'}) *)
    (* : Lemma (args `L.index` i == (L.map elab_pat_arg rd_pat_vars) `L.index` i) *)
    (* = *)
    (*   calc (==) { *)
    (*     L.map elab_pat_arg rd_pat_vars `L.index` i; *)
    (*     == { lemma_map_index elab_pat_arg rd_pat_vars i } *)
    (*     elab_pat_arg (rd_pat_vars `L.index` i); *)
    (*     == { () } *)
    (*     elab_pat_arg (Some?.v (readback_pat_var (args `L.index` i))); *)
    (*     == { Sealed.sealed_singl (Sealed.seal RT.tun) (R.Pat_Var?.sort (fst (args `L.index` i))) } *)
    (*     args `L.index` i; *)
    (*   } *)
    (* in *)
    (* Classical.forall_intro aux1; *)
    (* FStar.List.Tot.Properties.index_extensionality  *)
    (*     (L.map elab_pat_arg rd_pat_vars) *)
    (*     args; *)

    (* assert (fv == fv'); *)
    (* assume (us_opt == us_opt'); *)
    (* assert (args == args'); *)
    (* () *)
  | R.Pat_Constant c -> ()
  | R.Pat_Var st nm ->
    Sealed.sealed_singl st (Sealed.seal RT.tun);
    ()
  | _ -> ()

let check_match
        (g:env)
        (sc:term)
        (brs:list branch)
        (pre:term)
        (pre_typing: tot_typing g pre tm_vprop)
        (post_hint:post_hint_for_env g)
        (check:check_t)
  : T.Tac (checker_result_t g pre (Some post_hint))
  =
  let orig_brs = brs in
  let (| sc, sc_ty, sc_typing |) = check_term g sc in
  let elab_pats = L.map elab_pat (L.map fst brs) in

  let (| elab_pats', bnds', complete_d |) : (pats : list R.pattern & list (list R.binding) & pats_complete g sc sc_ty pats) =
    match T.check_match_complete (elab_env g) (elab_term sc) (elab_term sc_ty) elab_pats with
    | None -> fail g (Some sc.range) "Could not check that match is correct"
    | Some (| elab_pats, bnds, tok |) ->
      (| elab_pats, bnds, PC_Elab _ _ _ _ _ (RT.MC_Tok _ _ _ _ _ tok) |)
  in
  let new_pats = map_opt readback_pat elab_pats' in 
  if None? new_pats then
    fail g (Some sc.range) "failed to readback new patterns";
  let brs = zipWith (fun p (_, e) -> (p,e)) (Some?.v new_pats) brs in
  assume (L.length brs == L.length bnds');
  let (| brs, c, brs_d |) = check_branches g pre pre_typing post_hint check brs bnds' in
  assume (L.map (fun (p, _) -> elab_pat p) brs == elab_pats'); // provable
  (| _,
     c,
     T_Match g sc _ (E sc_typing) c brs brs_d complete_d |)
