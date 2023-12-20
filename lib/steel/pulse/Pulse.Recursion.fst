module Pulse.Recursion

module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
module T = FStar.Tactics.V2
open FStar.Tactics.V2
module RU = Pulse.RuntimeUtils

open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
module P = Pulse.Syntax.Printer

exception Splitlast_empty

let rec splitlast #a (l : list a) : Tac (list a & a) =
  match l with
  | [] -> raise Splitlast_empty
  | [x] -> [], x
  | x::xs ->
    let init, last = splitlast xs in
    x::init, last

 exception Map2_length_mismatch

let rec map2 #a #b #c (f : a -> b -> Tac c) (xs : list a) (ys : list b) : Tac (list c) =
  match xs, ys with
  | [], [] -> []
  | x::xx, y::yy -> f x y :: map2 f xx yy
  | _ -> raise Map2_length_mismatch

let debug_main g (s: unit -> Tac string) : Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.main"
  then print (s ())
  else ()

let string_as_term (s:string) : R.term =
  R.pack_ln (R.Tv_Const (C_String s))

let add_knot (g : env) (rng : R.range)
             (d : decl{FnDefn? d.d})
: Tac (d:decl{FnDefn? d.d})
=
  let FnDefn { id; isrec; bs; comp; meas; body } = d.d in
  if Nil? bs then
    fail g (Some d.range) "main: FnDefn does not have binders";
  (* NB: bs and comp are open *)
  let r_res = elab_comp comp in
  let elab_b (qbv : option qualifier & binder & bv) : Tot Tactics.NamedView.binder =
    let q, b, bv = qbv in
    {
      uniq = bv.bv_index;
      ppname = b.binder_ppname.name;
      sort = elab_term b.binder_ty;
      qual = elab_qual q;
      attrs = [];
    }
  in
  debug_main g
    (fun _ -> Printf.sprintf "add_knot: bs = %s\n"
              (string_of_list (fun (_, b,_) -> P.binder_to_string b) bs));

  (* for
       fn rec f (x1:t1) ... (xn:tn) :
         requires pre
         returns x:a
         ensures post

    we elab into

       let  f (x1:t1) ... (xn:tn)
              (f : (x1':t1) -> ... -> (xn':tn) -> stt a pre post)
              : stt a pre post

    without any sort of termination check. Now, for

       ghost fn rec f (x1:t1) ... (xn:tn) :
         requires pre
         returns x:a
         ensures post
         measure meas

    we must elab into

       let  f (x1:t1) ... (xn:tn)
              (f : (x1':t1) -> ... -> (xn':tn){meas' << meas} -> stt a pre post)
              : stt a pre post

    so we need to add the measure refinement. Since `meas` is an
    open term (wrt x1...xn), we must substitute it to create meas',
    subtituting x1' for x1, ..., xn' for xn

  *)
  (* Desugaring added a recursive knot argument at the end *)
  let bs, b_knot = splitlast bs in
  (* freshen *)
  let r_bs0 = List.Tot.map elab_b bs in
  let freshen_binder (b:T.binder) : T.binder =
    { b with uniq = 10000 + b.uniq
           ; ppname = map_seal b.ppname (fun s -> s ^ "'") }
  in
  let r_bs = map freshen_binder r_bs0 in
  let binder_to_r_namedv (b:T.binder) : R.namedv =
    R.pack_namedv {
      uniq = b.uniq;
      sort = seal b.sort;
      ppname = b.ppname;
    }
  in
  let prime_subst = map2 (fun (b1 b2 : T.binder) ->
                      R.NT (binder_to_r_namedv b1)
                            (binder_to_term b2)) r_bs0 r_bs in
  let r_bs =
    (* If ghost/atomic, we need to add a decreases refinement on the last arg *)
    if C_STAtomic? comp || C_STGhost? comp then (
      if None? meas then (
        let open FStar.Stubs.Pprint in
        let open Pulse.PP in
        fail_doc g (Some d.range) [
          text "'ghost' and 'atomic' recursive functions require a 'decreases' clause"]
      );
      let init, last = splitlast r_bs in
      let last : FStar.Tactics.NamedView.binder = last in
      let last =
        (* add a refinement to last *)
        let b' : simple_binder = {
          uniq = last.uniq;
          ppname = last.ppname;
          sort = last.sort;
          qual = Q_Explicit;
          attrs = [];
        }
        in
        let meas = Some?.v meas in
        let meas = elab_term meas in
        let meas' = R.subst_term prime_subst meas in
        let ref = `(`#meas' << `#meas) in
        (* TODO: this is not always printed *)
        let ref = (`labeled range_0 "Could not prove termination" (`#ref)) in
        { last with
            sort = (pack (Tv_Refine b' ref))
        }
      in
      init @ [last]
    ) else
      r_bs
  in
  let r_res = R.subst_term prime_subst r_res in
  let r_ty = FStar.Tactics.V2.SyntaxHelpers.mk_tot_arr r_bs r_res in
  // let open FStar.Stubs.Pprint in
  // let open Pulse.PP in
  // warn_doc g (Some d.range) [
  //   text "r_ty (type of the knot binder) =" ^/^ pp r_ty
  // ];
  if R.Tv_Unknown? (inspect_ln r_ty) then
    fail g (Some d.range) "error: r_ty is Tv_unknown in add_knot?";
  let b_knot =
    let s, rng = inspect_ident id in
    let b = mk_binder s rng (tm_fstar r_ty rng) in
    let bv = {
      bv_index = b_knot._3.bv_index;
      bv_ppname = { name = seal s; range = rng }
    } in
    let q = None in
    (q, b, bv)
  in
  let id' =
    let s, rng = inspect_ident id in
    pack_ident ("__recaux_" ^ s, rng)
  in
  let bs' = bs @ [b_knot] in

  (* NB: body and comp unchanged, they are already shifted properly
     (we dropped one binder and added one) *)
  { d with d =
    FnDefn { id=id'; isrec=false; bs=bs'; comp; meas=None; body }
  }

let tie_knot (g : env)  (rng : R.range)
             (nm_orig nm_aux : string)
             (d : decl) (r_typ : R.typ) (blob:RT.blob)
: Tac (list (RT.sigelt_for (fstar_env g)))
=
  let knot_r_typ =
    (* Remove the last arguments from r_typ, as that is the recursive knot.
    After doing that, we now have the needed type for elaboration. *)
    let bs, c = collect_arr_bs r_typ in
    if Nil? bs then fail g (Some rng) "tie_knot: impossible (1)";
    let bs = init bs in
    if Nil? bs then fail g (Some rng) "tie_knot: impossible (2)";
    mk_arr bs c
  in
  (* This is a temporary implementation. It will just create
  a new letbinding at the appropriate type with a `RU.magic()` body. *)
  let flag, sig, _ = RT.mk_unchecked_let (fstar_env g) nm_orig (`(magic())) knot_r_typ in
  let nm = string_as_term nm_aux in 
  let sig = RU.add_attribute sig (`("pulse.recursive.knot", `#(nm))) in
  [flag,sig,Some blob]
