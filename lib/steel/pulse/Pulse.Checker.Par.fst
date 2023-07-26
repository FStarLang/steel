module Pulse.Checker.Par

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common
open Pulse.Checker.Comp
open Pulse.Syntax.Printer

open FStar.Reflection.V2.TermEq

open FStar.Printf

module FV = Pulse.Typing.FV
module MT = Pulse.Typing.Metatheory

open FStar.Algebra.CommMonoid.Equiv
open FStar.Squash
// Instantiation of the comm monoid interface for vprop
(*
type equiv (a:Type) =
  | EQ :
    eq:(a -> a -> Type0) -> 
    reflexivity:(x:a -> Lemma (x `eq` x)) ->
    symmetry:(x:a -> y:a -> Lemma (requires (x `eq` y)) (ensures (y `eq` x))) ->
    transitivity:(x:a -> y:a -> z:a -> Lemma (requires (x `eq` y /\ y `eq` z)) (ensures (x `eq` z))) ->
    equiv a
*)

let ve_assoc_rev #g t0 t1 t2:
  vprop_equiv g (tm_star (tm_star t0 t1) t2) (tm_star t0 (tm_star t1 t2))
= VE_Sym g _ _ (VE_Assoc _ t0 t1 t2)

let symmetry_vprop_equiv g x y:
  Lemma (requires (vprop_equiv g x y)) (ensures (vprop_equiv g y x))
= let xy: squash (vprop_equiv g x y) = () in
bind_squash xy (fun eq_xy -> return_squash (VE_Sym g x y eq_xy))

let transitivity_vprop_equiv g x y z:
  Lemma (requires (vprop_equiv g x y /\ vprop_equiv g y z))
  (ensures (vprop_equiv g x z))
= let xy: squash (vprop_equiv g x y) = () in
let yz: squash (vprop_equiv g y z) = () in
bind_squash xy (fun eq_xy -> bind_squash yz
(fun eq_yz -> return_squash (VE_Trans g x y z eq_xy eq_yz)))

let vprop_equiv_equiv (g: env): equiv vprop
= EQ (vprop_equiv g)
(fun x -> Squash.return_squash (VE_Refl g x))
(symmetry_vprop_equiv g)
(transitivity_vprop_equiv g)

(*
type cm (a:Type) (eq:equiv a) =
  | CM :
    unit:a ->
    mult:(a -> a -> a) ->
    identity : (x:a -> Lemma ((unit `mult` x) `EQ?.eq eq` x)) ->
    associativity : (x:a -> y:a -> z:a ->
                      Lemma ((x `mult` y `mult` z) `EQ?.eq eq` (x `mult` (y `mult` z)))) ->
    commutativity:(x:a -> y:a -> Lemma ((x `mult` y) `EQ?.eq eq` (y `mult` x))) ->
    congruence:(x:a -> y:a -> z:a -> w:a -> Lemma (requires (x `EQ?.eq eq` z /\ y `EQ?.eq eq` w)) (ensures ((mult x y) `EQ?.eq eq` (mult z w)))) ->
    cm a eq
*)
let vprop_equiv_identity g x:
  Lemma (vprop_equiv g (tm_star tm_emp x) x)
= return_squash (VE_Unit g x)

let vprop_equiv_associativity g x y z:
  Lemma (vprop_equiv g (tm_star (tm_star x y) z) (tm_star x (tm_star y z)))
= return_squash (VE_Sym g _ _ (VE_Assoc g x y z))

let vprop_equiv_commutativity g x y:
  Lemma (vprop_equiv g (tm_star x y) (tm_star y x))
= return_squash (VE_Comm g x y)

let vprop_equiv_congruence g x y z w:
  Lemma (requires (vprop_equiv g x z /\ vprop_equiv g y w))
  (ensures (vprop_equiv g (tm_star x y) (tm_star z w)))
= let xz: squash (vprop_equiv g x z) = () in
  let yw: squash (vprop_equiv g y w) = () in
  bind_squash xz (fun eqxz -> bind_squash yw (
    fun eqyw -> return_squash (VE_Ctxt g x y z w eqxz eqyw)
  ))

let vprop_monoid g:
  cm vprop (vprop_equiv_equiv g)
= CM tm_emp tm_star
(vprop_equiv_identity g)
(vprop_equiv_associativity g)
(vprop_equiv_commutativity g)
(vprop_equiv_congruence g)

// End: Instantiation of vprop_equiv g and star as commutative monoid

let print_term (t: term): T.Tac unit
  = T.print (term_to_string t)

let rec print_list_terms' (l: list term): T.Tac unit
= match l with
| [] -> T.print "]"
| t::q -> (T.print ", "; print_term t; print_list_terms' q)

let print_list_terms (l: list term): T.Tac unit
  = match l with
  | [] -> T.print "[]"
  | t::q -> (T.print "["; print_term t; print_list_terms' q)

let indent (level:string) = level ^ " "

let st_equiv_to_string (#g: env) #c1 #c2 (level: string) (eq: st_equiv g c1 c2)
  : T.Tac string
  = (*if comp_pre c1 = comp_pre c2 && comp_post c1 = comp_post c2
    then T.print "Trivial equivalence!"
    else T.print "Somehow non-trivial equivalence...";*)
    sprintf "st_equiv\n%s pre1: %s\n%s pre2: %s\n%s post1: %s\n%s post2: %s"
  //pre: (%s) (%s)) (post: (%s) (%s))"
  level
  (term_to_string (comp_pre c1))
  level
  (term_to_string (comp_pre c2))
  level
  (term_to_string (comp_post c1))
  level
  (term_to_string (comp_post c2))

#push-options "--z3rlimit 10"
let rec st_typing_to_string' (#g:env) (#t:st_term) (#c:comp) (level: string) (ty: st_typing g t c)
//let rec st_typing_to_string (ty: st_typing)
  : T.Tac string
  = match ty with
    | T_Abs g x q b u body c _ _ -> "T_Abs"
    | T_STApp g head _ q res arg _ _ -> "T_STapp"
    | T_Return g c use_eq u t e post x _ _ _ -> "T_Return"
    | T_Lift g e c1 c2 _ _ -> "T_Lift"
    | T_Bind g e1 e2 c1 c2 b _ c ty1 _ ty2 _ ->
      sprintf "T_Bind \n (%s); \n (%s)"
      (st_typing_to_string' (indent level) ty1)
      (st_typing_to_string' (indent level) ty2)
    | T_TotBind g e1 e2 t1 c2 x _ ty' ->
      sprintf "T_TotBind (%s)"
      (st_typing_to_string' (indent level) ty')
    | T_Frame g e c frame _ ty' ->
      sprintf "T_Frame (frame=%s) (\n%s%s)"
      (term_to_string frame)
      level
      (st_typing_to_string' (indent level) ty')
    | T_Equiv g e c c' ty' equiv ->
      sprintf "T_Equiv (%s) (\n%s%s)"
      //(st_equiv_to_string level equiv)
      "..."
      level
      (st_typing_to_string' (indent level) ty')
    | T_Par g eL cL eR cR x _ _ ty1 ty2 -> "T_Par"
    | _ -> "Unsupported"
    // TODO: If

let st_typing_to_string (#g:env) (#t:st_term) (#c:comp) (ty: st_typing g t c)
  = st_typing_to_string' #g #t #c "" ty
//let st_typing_to_string #g #t #c (ty: st_typing g t c) = st_typing_to_string' "" ty



open Pulse.Checker.VPropEquiv

// Would need a stronger postcondition
// Like pre and post are equiv
// needs typing for one of the two pres...
let create_st_equiv
  (g: env)
  (c: comp_st)
  (c': comp_st{st_equiv_pre c c'})
  (equiv_pre: vprop_equiv g (comp_pre c) (comp_pre c'))
  //(typing_pre: either (tot_typing g (comp_pre c) tm_vprop) (tot_typing g (comp_pre c') tm_vprop))
  (typing_pre: tot_typing g (comp_pre c) tm_vprop)
  (typing_res: tot_typing g (comp_res c) (tm_type (comp_u c)))
  //(x:var{fresh....})
  //(equiv_post: x:var -> vprop_equiv g (comp_post c) (comp_post c'))
: st_equiv g c c'
= let x = fresh g in
  assume ( ~(x `Set.mem` freevars (comp_post c)) /\
          ~(x `Set.mem` freevars (comp_post c')) );
  //assume (st_equiv_pre c c');
  (*
  let tot1: Ghost.erased (tot_typing g (comp_pre c) tm_vprop) = (
    match typing_pre with
    | Inl ty -> ty
    | Inr ty -> (vprop_equiv_typing equiv_pre)._2 ty
  ) in
  *)
  let tot3: Ghost.erased (tot_typing (push_binding g x ppname_default (comp_res c)) (open_term (comp_post c) x) tm_vprop) = magic() in
  let equiv_post: Ghost.erased (vprop_equiv (push_binding g x ppname_default (comp_res c)) (open_term (comp_post c) x) (open_term (comp_post c') x)) = magic() in
  ST_VPropEquiv g c c' x typing_pre typing_res tot3 equiv_pre equiv_post

// TODO:
let inv_typing_comp_res #g #e (#c: comp{stateful_comp c}) (ty: st_typing g e c):
  tot_typing g (comp_res c) (tm_type (comp_u c))
= admit()

let inv_typing_comp_pre #g #e (#c: comp{stateful_comp c}) (ty: st_typing g e c):
  tot_typing g (comp_pre c) tm_vprop
= admit()

// This function replaces T_Frame with empty frames by T_Equiv
let rec replace_frame_emp_with_equiv #g #t #c (ty: st_typing g t c):
  Tot (st_typing g t c) (decreases ty)
  = match ty with
  | T_Frame g e c' frame tot_ty ty' -> 
  // comp_pre c = comp_pre_pre (add_frame c')
  if Tm_Emp? frame.t then
    let pre = comp_pre c' in
    let eq1: vprop_equiv g (tm_star frame pre) pre = VE_Unit g pre in
    let eq2: vprop_equiv g (tm_star pre frame) (tm_star frame pre) = VE_Comm g pre frame in
    let eq3: vprop_equiv g (tm_star pre frame) pre = VE_Trans g _ _ _ eq2 eq1 in
    let eq_pre: vprop_equiv g (comp_pre c') (tm_star (comp_pre c') frame) = VE_Sym g _ _ eq3 in
    let typing_res: tot_typing g (comp_res c) (tm_type (comp_u c)) = inv_typing_comp_res ty' in
    let st_eq: st_equiv g c' c = create_st_equiv g c' c eq_pre (inv_typing_comp_pre ty') typing_res in
      T_Equiv g e c' c (replace_frame_emp_with_equiv ty') st_eq
  else ty
  | T_Equiv g e c c' ty' equiv ->
  T_Equiv g e c c' (replace_frame_emp_with_equiv ty') equiv
  | T_Bind g e1 e2 c1 c2 b x c ty1 tot1 ty2 tot2 ->
  T_Bind g e1 e2 c1 c2 b x c (replace_frame_emp_with_equiv ty1) tot1 (replace_frame_emp_with_equiv ty2) tot2
  | _ -> ty

(*
// This function collapses two consecutive nested T_Equiv into one
let rec collapse_equiv #g #e #c (ty: st_typing g e c):
  //Tot (st_typing g e c) (decreases ty)
  T.Tac (st_typing g e c)
  = match ty with
  // Pattern: T_Equiv g e c' c ...
  | T_Equiv _ _ c' _ (T_Equiv _ _ c'' _ ty' eq') eq ->
  let st_eq: st_equiv g c'' c =
    create_st_equiv g c'' c (VE_Trans g _ _ _ (ST_VPropEquiv?.equiv_pre eq') (ST_VPropEquiv?.equiv_pre eq)) in
  collapse_equiv (T_Equiv g e c'' c ty' st_eq)
  | T_Equiv _ _ c' _ ty' eq -> T_Equiv g e c' c (collapse_equiv ty') eq
  | T_Bind g e1 e2 c1 c2 b x c ty1 tot1 ty2 tot2 ->
  T_Bind g e1 e2 c1 c2 b x c (collapse_equiv ty1) tot1 (collapse_equiv ty2) tot2
  | _ -> ty
  *)

let rec collect_frames #g #e #c (ty: st_typing g e c):
  T.Tac ((l:list term{length l > 0}) & tot_typing g (hd l) tm_vprop)
= match ty with
  | T_Frame g e c' frame tot_ty ty' -> (| [frame], tot_ty |)
  | T_Equiv g e c c' ty' equiv -> collect_frames ty'
  | T_Bind g e1 e2 c1 c2 b x c ty1 _ ty2 _ -> 
  let (| l1, tot1 |) = collect_frames ty1 in
  let (| l2, _ |) = collect_frames ty2 in
  (| l1 @ l2, tot1 |)
  | _ -> T.fail "Unable to figure out frame at this leaf"
 
 // Needed
let simplify_st_typing #g #e #c (ty: st_typing g e c): T.Tac (st_typing g e c)
  = //collapse_equiv (replace_frame_emp_with_equiv ty)
  replace_frame_emp_with_equiv ty

(*
let deq (a: host_term) (b: host_term): (r:bool{r <==> (a == b)}) =
  (assume (faithful a); assume (faithful b); term_eq_dec a b)

let delta (a: host_term) (b: host_term): nat
  = if deq a b then 1 else 0
  *)

//open FStar.Seq

//let seqterm = seq host_term

(*
TODO:
let rec countt (l: seqterm) (x: host_term): nat
  = match l with
  | [] -> 0
  | t::q -> delta t x + countt q x
  *)

//let single (#a: Type) (x: a): seq a = create 1 x

//let prepend (#a: Type) (t: a) (q: seq a) = Seq.append (single t) q

//let atom = (t:term{~(Tm_Star? t.t) /\ ~(Tm_Emp? t.t)})
let atom = term

let typed_list_atoms g = list (x:atom & tot_typing g x tm_vprop)
// is destructive
let rec compute_intersection_aux g (ft: atom) (ty: tot_typing g ft tm_vprop) (l: list atom):
  Tot (typed_list_atoms g & list atom)
  (decreases (length l))
  = match l with
  | [] -> ([], [])
  | t::q -> if eq_tm t ft then ([(| ft, ty |) ], q)
  else let (a, b) = compute_intersection_aux g ft ty q in (a, t::b)
  (*
  if Seq.length l = 0 then (Seq.empty, Seq.empty)
  else (let (t, q) = (head l, tail l) in
    if deq ft t then (Seq.create 1 ft, q)
    else let (a, b) = compute_intersection_aux ft q in (a, prepend t b)
  *)
  (*
  // how to link
  // delta t x = countt l x - countt b x
  *)

// spec
(*
let rec countt_compute_intersection (ft: host_term) (l: seqterm) (x: host_term):
  Lemma (let (a, b) = compute_intersection_aux ft l in (countt l x = countt a x + countt b x
  /\ length a <= 1 /\ length l = length a + length b
  /\ countt a x <= 1
  /\ (~(deq ft x) ==> countt a x = 0)
  /\ (countt a x = 1 <==> (deq ft x /\ countt l x >= 1))
  ))
= match l with
  | [] -> ()
  | t::q -> if deq ft t then ()
  else countt_compute_intersection ft q x
  *)

// Could be improved (in terms of performance) if we had an order on host_terms
let rec compute_intersection g (l1: typed_list_atoms g) (l2: list atom):
  Tot (typed_list_atoms g) (decreases (length l1))
 = match l1 with
  | [] -> []
  | t::q -> let (a, b) = compute_intersection_aux g t._1 t._2 l2 // l2 = a @ b
  in a @ compute_intersection g q b
 (*
  if length l1 = 0 then Seq.empty
  else (let (t, q) = (head l1, tail l1) in
    let (a, b) = compute_intersection_aux t l2 // l2 = a @ b
    in append a (compute_intersection q b)
  )
  *)

(*
let rec countt_append (l1: seqterm) (l2: seqterm) (x: host_term):
  Lemma (countt (l1 @ l2) x = countt l1 x + countt l2 x)
  = match l1 with
  | [] -> ()
  | t::q -> countt_append q l2 x

let rec compute_intersection_included (l1: seqterm) (l2: seqterm) (x: host_term):
  Lemma (let l = compute_intersection l1 l2 in
  countt l x = min (countt l1 x) (countt l2 x))
= match l1 with
  | [] -> ()
  | t::q -> let (a, b) = compute_intersection_aux t l2 in
   countt_compute_intersection t l2 x;
  calc (=) {
    countt (compute_intersection l1 l2) x;
    = { countt_append a (compute_intersection q b) x }
    countt a x + countt (compute_intersection q b) x;
    = { compute_intersection_included q b x }
    countt l2 x - countt b x + min (countt q x) (countt b x);
    = {}
    min (countt q x - countt b x + countt l2 x) (countt l2 x);
    = {}
    min (countt l1 x) (countt l2 x);
  }
  *)


(*
let add_range t = with_range (Tm_FStar t) (Range.range_0)

let from_list_to_term (g: env) (l: seqterm): term
  = let l' = map_seq add_range l in
  FStar.Seq.Permutation.foldm_snoc (vprop_monoid g) l'
  //tm_star tm_emp l'

//let term_to_list_inv
// Not correct...

let from_list_to_term_single g ft
: Lemma (vprop_equiv g (from_list_to_term g (single ft)) (add_range ft))
= 
  map_seq_create add_range 1 ft;
  Seq.Permutation.foldm_snoc_singleton (vprop_monoid g) (add_range ft)

(*assert (index (single ft) 0 == ft)
  map_seq_create add_range 1 ft;
  assert (map_seq add_range (single ft) == single (add_range ft))
  //map_seq_index add_range (single ft) 0
  *)



// collects a subset of all host terms
// should collect typing proofs as well
let rec term_to_list (t: term): seqterm
  = match t.t with
  | Tm_FStar ft -> single ft
  | Tm_Star l r -> append (term_to_list l) (term_to_list r)
  | _ -> admit() //T.fail "Could not convert the term to a list"
  *)

//let vprop_as_list_atom (t: vprop): (list atom)
//  = (assume false; vprop_as_list t)

let rec vprop_as_list_typed #g (vp:term) (ty: tot_typing g vp tm_vprop)
  : typed_list_atoms g// list (x:atom & tot_typing g x tm_vprop)
  = match vp.t with
    | Tm_Emp -> []
    | Tm_Star vp0 vp1 ->
    vprop_as_list_typed vp0 (star_typing_inversion_l #g #vp0 #vp1 ty)
    @ vprop_as_list_typed vp1 (star_typing_inversion_r #g #vp0 #vp1 ty)
    | _ -> [(| vp, ty|)]

//let rec compute_intersection g (l1: typed_list_atoms g) (l2: list atom):
//  Tot (typed_list_atoms g) (decreases (length l1))

let compute_intersection_list g (l: list term{length l > 0}) (ty: tot_typing g (hd l) tm_vprop):
  T.Tac (list (x:atom & tot_typing g x tm_vprop))
  = match l with
  | [] -> []
  | t::q -> fold_left (compute_intersection g) (vprop_as_list_typed t ty) (map vprop_as_list q)

let rec list_of_FStar_term_to_string l: T.Tac string
= match l with
  | [] -> ""
  | t::q -> T.term_to_string t ^ ", " ^ list_of_FStar_term_to_string q

(*
let rec remove_host_term_from_term (ht: host_term) (t: term): bool & term
// returns (b, t')
// b means we have removed it successfully, and t' is t minus ht
// b false implies t = t'
  = match t.t with
  | Tm_FStar ft -> if deq ft ht then (assert (ht == ft); (true, with_range Tm_Emp t.range)) else (false, t)
  | Tm_Star l r -> let (b, l') = remove_host_term_from_term ht l in
  if b then (true, with_range (Tm_Star l' r) t.range)
  else let (b', r') = remove_host_term_from_term ht r in
    if b' then (true, with_range (Tm_Star l r') t.range) else (false, t)
  | _ -> (false, t)
// should return true in every "good" call

let rec remove_from_vprop (l: seqterm) (t: term):
  T.Tac term
  // need to prove that it's equiv...
= if length l = 0 then t
  else let (ht, q) = (head l, tail l) in remove_from_vprop q ((remove_host_term_from_term ht t)._2)
(*match l with
  | [] -> t
  | ht::q -> remove_from_vprop q ((remove_host_term_from_term ht t)._2)
  *)
  *)

(*
let rec remove_from_vprop_equiv g (l: seqterm) (t: term):
  T.Tac (vprop_equiv g t (tm_star (from_list_to_term g l) (remove_from_vprop l t)))
= admit()
*)

let adapt_st_comp (c: st_comp) (pre: vprop) (post: vprop): st_comp =
  { u = c.u; res = c.res; pre = pre; post = post }

//let star_with_range r a b = with_range (Tm_Star a b) r


let ve_unit_rev (g: env) (t:term): vprop_equiv g (tm_star t tm_emp) t
  = let eq1: vprop_equiv g (tm_star tm_emp t) t = VE_Unit _ t in
  let eq2: vprop_equiv g (tm_star t tm_emp) (tm_star tm_emp t)
  = VE_Comm _ _ _ in
  VE_Trans _ _ _ _ eq2 eq1

  // need to show that appending is OK?
  (*
let append_from_list_to_term_equiv (g: env) (l1 l2: seqterm):
  Lemma (vprop_equiv g
    (from_list_to_term g (append l1 l2))
    (tm_star (from_list_to_term g l1) (from_list_to_term g l2))
    )
= FStar.Seq.Permutation.foldm_snoc_append (vprop_monoid g) (map_seq add_range l1) (map_seq add_range l2);
  map_seq_append add_range l1 l2;
  ()
  *)

// if there 
//let unsquash_test (#p: Type) (s: squash p): GTot p
//  = admit()
open FStar.IndefiniteDescription

(*
let rec term_to_list_vprop_equiv (g: env) (t: term):
  T.Tac (vprop_equiv g t (from_list_to_term g (term_to_list t)))
= match t.t with
  | Tm_FStar ft -> VE_Sym g _ _ (elim_squash (from_list_to_term_single g ft))
  | Tm_Star l r -> 
  let eql = term_to_list_vprop_equiv g l in
  let eqr = term_to_list_vprop_equiv g r in
  let ll = term_to_list l in
  let rr = term_to_list r in
  let eqlr: vprop_equiv g (tm_star l r) (tm_star (from_list_to_term g ll) (from_list_to_term g rr))
  = VE_Ctxt g _ _ _ _ eql eqr in
  append_from_list_to_term_equiv g ll rr;
  let eq_append: vprop_equiv g
    (tm_star (from_list_to_term g ll) (from_list_to_term g rr))
    (from_list_to_term g (append ll rr))
   = VE_Sym _ _ _ (elim_squash ()) in
  //let sq: squash (vprop_equiv g (from_list_to_term g (append ll rr)) (from_list_to_term g (term_to_list t))) = () in
  //let eq_append: vprop_equiv g _ (from_list_to_term g (term_to_list t)) = VE_Sym _ _ _ sq in
  VE_Trans g _ _ _ eqlr eq_append
  | _ -> fail g None "Could not convert term to an equivalent list representation"
*)

open Pulse.Checker.Framing

let remove_from_vprop #g (#ctxt: term) (inter: term) (ctxt_typing: tot_typing g ctxt tm_vprop):
  T.Tac
  (res:term & tot_typing g res tm_vprop & vprop_equiv g (tm_star inter res) ctxt)
= match check_frameable ctxt_typing inter with
| Inl x -> x
| Inr _ -> fail g None "Failure to remove intersection from frame..."


let rec extract_common_frame #g #t #c #inter
  (inter_typed: Ghost.erased (tot_typing g inter tm_vprop)) (ty: st_typing g t c):
  T.Tac (st_typing g t c) (decreases ty)
  = match ty with
  | T_Frame g e c0 frame tot_ty ty' ->
  let (| f1, tot_ty1, eq_21_f |) = remove_from_vprop inter tot_ty in
  let c1 = add_frame c0 f1 in
  let f2 = inter in
  let eq_12_f: vprop_equiv g (tm_star f1 f2) frame = VE_Trans _ _ _ _ (VE_Comm _ f1 f2) eq_21_f in
  let eqf12: vprop_equiv g frame (tm_star f1 f2) = VE_Sym _ _ _ eq_12_f in
  let c2 = add_frame c1 f2 in
  let tot_ty2: Ghost.erased (tot_typing g f2 tm_vprop) = inter_typed in
  let ty1 = T_Frame g e c0 f1 tot_ty1 ty' in
  let ty2 = T_Frame g e c1 f2 tot_ty2 ty1 in
  let pre = comp_pre c0 in
  let eq': vprop_equiv g (tm_star pre (tm_star f1 f2)) (tm_star pre frame) =
    VE_Ctxt g _ _ _ _ (VE_Refl g pre) (VE_Sym g _ _ eqf12) in
  let eq_assoc: vprop_equiv g (tm_star (tm_star pre f1) f2) (tm_star pre (tm_star f1 f2))
    = VE_Sym _ _ _ (VE_Assoc _ _ _ _) in
  let needed_eq: vprop_equiv g (tm_star (tm_star pre f1) f2) (tm_star pre frame) =
    VE_Trans _ _ _ _ eq_assoc eq'
  in
  let typing_pre_c0: tot_typing g (comp_pre c0) tm_vprop = inv_typing_comp_pre ty' in
  let typing_pre_c1: tot_typing g (comp_pre c1) tm_vprop = star_typing #g #(comp_pre c0) #f1 typing_pre_c0 tot_ty1 in
  let typing_pre_c2: tot_typing g (comp_pre c2) tm_vprop = star_typing #g #(comp_pre c1) #f2 typing_pre_c1 inter_typed in
  let typing_res: tot_typing g (comp_res c2) (tm_type (comp_u c2)) = inv_typing_comp_res ty' in
  let st_eq: st_equiv g c2 c = create_st_equiv g c2 c needed_eq typing_pre_c2 typing_res in
  T_Equiv g e c2 c ty2 st_eq
  // replace frame by frame-common, and put that into common frame
  // and an equiv
  // Example: frame = A * B * C
  // Common: B
  // Result:
  // Equiv (A * B * C) ((A * C) * B)
  // {
  //    Frame B (Frame (A * C) ... )
  // }
  | T_Equiv g e c c' ty' equiv ->
  T_Equiv g e c c' (extract_common_frame inter_typed ty') equiv
  | T_Bind g e1 e2 c1 c2 b x c ty1 tot1 ty2 tot2 ->
  assert (fresh_wrt x g Set.empty);
  let ntyped: Ghost.erased (tot_typing _ inter tm_vprop)
    = Pulse.Typing.Metatheory.tot_typing_weakening x (comp_res c1) inter_typed in
  T_Bind g e1 e2 c1 c2 b x c (extract_common_frame inter_typed ty1) tot1 (extract_common_frame #_ #_ #_ #inter ntyped ty2) tot2
  | _ -> fail g None "No common frame to extract..." // bad, should not happen

#push-options "--z3rlimit 20 --admit_smt_queries true"

#set-options "--split_queries always --query_stats"

let bring_frame_top_bind #g #e1 #c1' #e2 #c2' #c #c1 #c2
(b:binder { b.binder_ty == comp_res c1' })
(x: var{None? (lookup g x)  /\ ~(x `Set.mem` freevars_st e2) })
(ty1:st_typing g e1 c1'{T_Frame? ty1})
(ty2:st_typing (push_binding g x ppname_default (comp_res c1')) (open_st_term_nv e2 (b.binder_ppname, x)) c2'{T_Frame? ty2})
(bcomp: bind_comp g x c1 c2 c)
(eq1: st_equiv g c1' c1)
(eq2: st_equiv (push_binding g x ppname_default (comp_res c1')) c2' c2)
: T.Tac (c': comp & st_typing g (wr (Tm_Bind { binder=b; head=e1; body=e2 })) c' & st_equiv g c' c) 
=
match ty1 with
| T_Frame _ _ c1'' f1 totf1 ty1' -> (
    let ty1': st_typing g e1 c1'' = ty1' in
  match ty2 with
  | T_Frame _ _ c2'' f2 totf2 ty2' ->
    let g2 = push_binding g x ppname_default (comp_res c1') in
    let ty2': st_typing g2 _ c2'' = ty2' in
    let b':(b':binder{Mkbinder?.binder_ty b' == comp_res c1'}) =
      {
        binder_ty = comp_res c1'; binder_ppname = b.binder_ppname
      } in
    (
      assume (bind_comp_compatible c1' c2');
      assume (f1 == f2);
      assume (bind_comp_pre x c1'' c2'');
      let c': comp_st = bind_comp_out c1'' c2'' in
      let tot_ty1: Ghost.erased (tot_typing g (comp_res c1') (tm_type (comp_u c1'))) = inv_typing_comp_res ty1 in
      let bcomp': bind_comp g x c1'' c2'' c' = Bind_comp g x c1'' c2'' (magic()) (magic()) (magic()) in
      //let (| e, c', ty' |)
      //= Pulse.Typing.Combinators.mk_bind g (comp_pre c1'') e1 e2 c1'' c2'' (Pulse.Syntax.Base.v_as_nv x) ty1' tot_ty1 ty2' (magic()) (magic())
      //in
      //let ty': st_typing _ _ _ = bound._1 in
      let ty': st_typing _ _ _ = T_Bind g e1 e2 c1'' c2'' b' x c' ty1' tot_ty1 ty2' bcomp' in
      let e: st_term = {range = e1.range; term = Tm_Bind {binder=b; head=e1; body=e2}} in
      let c'': comp_st = add_frame c' f1 in
      let ty'': st_typing g _ c'' = T_Frame g e c' f1 totf1 ty' in
      let jeq: vprop_equiv g (comp_pre c'') (comp_pre c1) =
        VE_Trans _ _ _ _ (VE_Refl _ _) (ST_VPropEquiv?.equiv_pre eq1) in
      let typing_res: tot_typing g (comp_res c'') (tm_type (comp_u c'')) = inv_typing_comp_res ty'' in
      let typing_pre: tot_typing g (comp_pre c'') tm_vprop = inv_typing_comp_pre ty'' in
      let eq: st_equiv g c'' c = create_st_equiv g c'' c jeq typing_pre typing_res in
      Mkdtuple3 c'' ty'' eq)
  | _ -> fail g None "Unexpected issue while bringing the frame to the top"
)
// | _ -> fail g None "Unexpected issue while bringing the frame to the top" #pop-options
#pop-options
#set-options "--z3rlimit 40 --split_queries no"

// RENAME
let lem1 g x c1 c2 c (d : bind_comp g x c1 c2 c)
 : universe_of g (comp_res c2) (comp_u c2)
 = match d with
   | Bind_comp _ _ _ _ r _ _ -> r 
   | Bind_comp_ghost_l _ _ _ _ _ r _ _ -> r
   | Bind_comp_ghost_r _ _ _ _ _ r _ _ -> r

// wrapper to make lemma below clearer
let comp_st_typing (g:env) (c:comp_st) : Type =
  st_comp_typing g (st_comp_of_comp c)

let cong_bind_l
  (g:env)
  (l1 l2 : comp_st)
  (d : st_equiv g l1 l2)
  (x : var)
  (r : comp_st{bind_comp_compatible l1 r})
  (rd : comp_st_typing g r)
  : T.Tac (st_equiv g (bind_comp_out l1 r) (bind_comp_out l2 r))
  =
    let c1 = bind_comp_out l1 r in
    let c2 = bind_comp_out l2 r in
    let xt = comp_res l1 in
    assert(bind_comp_compatible l1 r <==> bind_comp_compatible l2 r);
    let ST_VPropEquiv _ _ _ x l1_pre_typing l1_res_typing l1_post_typing
                      pre_equiv
                      post_equiv = d
    in
    let STC _ _ z r_res_typing r_pre_typing r_post_typing = rd in
    let y = fresh (push_binding g x ppname_default xt) in
    assume (~ (y `Set.mem` freevars (comp_post r))); // should be easily provable by extending argument above

    ST_VPropEquiv g c1 c2
     z l1_pre_typing r_res_typing r_post_typing pre_equiv (VE_Refl _ _)

let cong_bind_r
  (g:env)
  (l : comp_st)
  (ld : comp_st_typing g l)
  (x : var)
  (r1 : comp_st{bind_comp_compatible l r1})
  (r2 : comp_st{bind_comp_compatible l r2})
  (d : st_equiv g r1 r2)
  : T.Tac (st_equiv g (bind_comp_out l r1) (bind_comp_out l r2))
  = let c1 = bind_comp_out l r1 in
    let c2 = bind_comp_out l r2 in
    let xt = comp_res l in
    let STC _ _ x l_res_typing l_pre_typing l_post_typing = ld in
    let ST_VPropEquiv _ _ _ x r1_pre_typing r1_res_typing r1_post_typing
                      pre_equiv
                      post_equiv = d
    in
    ST_VPropEquiv g c1 c2
      x
      l_pre_typing
      r1_res_typing
      r1_post_typing
      (VE_Refl _ _)
      post_equiv

(*
// Up to equivalence...
let rec bring_frame_top' #g #t #c (ty: st_typing g t c):
// should allow to change the computation, as long as it's equivalent
// we put back the equiv at the end? Not really needed
  T.Tac (c': comp & st_equiv g c' c) //(decreases ty)
  =
  match ty with
  | T_Frame g e c0 frame tot_ty ty' -> // Frame already at the top: Good
  (
    Mkdtuple2 c (create_st_equiv g c c (VE_Refl _ _) (inv_typing_comp_pre ty) (inv_typing_comp_res ty))
  )
  | T_Equiv _ _ c1 _ ty1 eq1 -> 
    let eq1: vprop_equiv g (comp_pre c1) (comp_pre c) = ST_VPropEquiv?.equiv_pre eq1 in
    let (| c2, eq2 |) = bring_frame_top' ty1 in
    let ST_VPropEquiv _ _ _ _ typing_pre typing_res typing_post _ _ = eq2 in
    //let c2: comp = r._1 in
    //let eq2: st_equiv g c2 c1 = r._2 in
    let eq12: st_equiv g c2 c = create_st_equiv g c2 c
      (VE_Trans _ _ _ _ (ST_VPropEquiv?.equiv_pre eq2) eq1) typing_pre typing_res
    in
    Mkdtuple2 c2 eq12
  | T_Bind _ e1 e2 c1 c2 b x c ty1 _ ty2 bcomp2 ->
    assert (~(x `Set.mem` freevars (comp_post c2)));
    let _ = lem1 g x c1 c2 c bcomp2 in
    assert ((universe_of g (comp_res c2) (comp_u c2)));
    //assert (~(x `Set.mem` freevars (comp_res c2)));
    //assert (bind_comp_compatible c1 c2 || bind_comp_compatible);
    let (| c1', ceq1 |) = bring_frame_top' #_ #_ #_ ty1 in
    let (| c2', ceq2 |) = bring_frame_top' #(push_binding g x ppname_default (comp_res c1)) #_ #_ ty2 in
    // let (| c', cc, v, ty_post |) =
    //   match bcomp2 with
    //   | Bind_comp _ _ _ cc _ v ty_post -> (| bind_comp_out c1' c2', cc, v, ty_post |)
    //   | Bind_comp_ghost_l _ _ _ cc _ _ v ty_post -> (| bind_comp_ghost_l_out c1' c2', cc, v, ty_post |)
    //   | Bind_comp_ghost_r _ _ _ cc _ _ v ty_post -> (| bind_comp_ghost_r_out c1' c2', cc, v, ty_post |)
    // in
    assume (Bind_comp? bcomp2);
    let c' = bind_comp_out c1' c2' in
    let Bind_comp _ _ _ _ _ v ty_post = bcomp2 in

    let ST_VPropEquiv _ _ _ _ typing_pre1 typing_res1 typing_post1 _ _ = ceq1 in
    let ST_VPropEquiv _ _ _ z typing_pre2 typing_res2 typing_post2 _ equiv_post = ceq2 in
    //let typing_res2:
    //   tot_typing (push_binding g x ppname_default (comp_res c1)) (comp_res c2') (tm_type (comp_u c2')) = typing_res2 in
    // // _ is (push_binding g x ...)
    // let typing_res2: tot_typing g (comp_res c2') (tm_type (comp_u c2')) = magic() in
    // // assume (x == z);
    // // assert false;
    // // assume (z notin freevars c1)
    // let typing_post2: tot_typing _ (comp_post c2') tm_vprop = typing_post2 in
    // let typing_post2: tot_typing (push_binding g z ppname_default (comp_res c')) (comp_post c2') tm_vprop = magic() in
    // admit();
    let gx  = push_binding g  x ppname_default (comp_res c1') in
    let gxz = push_binding gx z ppname_default (comp_res c') in
    let gz  = push_binding g  z ppname_default (comp_res c') in

    let equiv_post
      : vprop_equiv gxz (open_term (comp_post c2') z) (open_term (comp_post c2) z) 
      = equiv_post
    in
    let equiv_post
      : vprop_equiv gz (open_term (comp_post c2') z) (open_term (comp_post c2) z) 
      = magic()
    in
    assert ((universe_of g (comp_res c2') (comp_u c2')));
    assert (~(x `Set.mem` freevars (comp_res c2)));
    let typing_res2: tot_typing gx (comp_res c2') (tm_type (comp_u c2')) = typing_res2 in
    let typing_res2: tot_typing g (comp_res c2') (tm_type (comp_u c2')) = magic() in
    // // _ is (push_binding g x ...)
    // let typing_res2: tot_typing g (comp_res c2') (tm_type (comp_u c2')) = magic() in
    // // assume (x == z);
    let typing_post2: tot_typing gxz (open_term (comp_post c2') z) tm_vprop = typing_post2 in
    let typing_post2: tot_typing gz (open_term (comp_post c2') z) tm_vprop = magic() in
    let ceq : st_equiv g c' c =
      ST_VPropEquiv g c' c
        z
        typing_pre1
        typing_res2
        typing_post2
        ceq1.equiv_pre
        equiv_post
    in
    (| c', ceq |)
    // let c2': comp = r2._1 in
    
    // (
    //   assert (None? (lookup g x));
    // let r1 = bring_frame_top ty1 in
    // let c1': comp = r1._1 in
    // let ty1: st_typing g e1 c1' = r1._2 in
    // let eq1: st_equiv g c1' c1 = r1._3 in
    // let g2 = push_binding g x ppname_default (comp_res c1) in
    // let t2 = (open_st_term_nv e2 (b.binder_ppname, x)) in
    // let r2: (c': comp & st_typing g2 t2 c' & st_equiv g2 c' c2) = bring_frame_top #g2 #t2 #c2 ty2 in
    // let c2': comp = r2._1 in
    // let ty2: st_typing g2 t2 c2' = r2._2 in
    // let eq2: st_equiv g2 c2' c2 = r2._3 in
    // let b' =
    //   {
    //     binder_ty = comp_res c1'; binder_ppname = b.binder_ppname
    //   } in
    // if T_Frame? ty1 && T_Frame? ty2 then
    //   (
    //     assert (b'.binder_ty == comp_res c1');
    //     assert (None? (lookup g x)  /\ ~(x `Set.mem` freevars_st e2));
    //     assert (push_binding g x ppname_default (comp_res c1') == g2);
    //     assert (open_st_term_nv e2 (b'.binder_ppname, x) == t2);
    //   let (b':binder{b'.binder_ty == comp_res c1'}) = b' in
    //   let (x:var{  None? (lookup g x)  /\ ~(x `Set.mem` freevars_st e2) }) = x in
    //   let (ty1:st_typing g e1 c1'{T_Frame? ty1}) = ty1 in
    //   let (ty2:st_typing (push_binding g x ppname_default (comp_res c1')) (open_st_term_nv e2 (b'.binder_ppname, x)) c2'{T_Frame? ty2}) = ty2 in
    //   let bcomp2:(bind_comp g x c1 c2 c') = bcomp2 in
    //   bring_frame_top_bind #g #e1 #c1' #e2 b' x ty1 ty2 bcomp2 eq1 eq2
    //   )
    // else
    //   fail g None "Should not have happened..."
    // )
  | _ -> fail g None "No frame to bring to the top..." // bad, should not happen


(*

// assuming ty is the typing derivation of the left branch
let get_typing_deriv_and_frame #g #t #c (ty: st_typing g t c):
  T.Tac (c':comp & st_typing g t c' & vprop) (decreases ty)
= let r = bring_frame_top ty in
  let c': comp = r._1 in
  let ty': st_typing g t c' = r._2 in
  (
    //T.print "Bringing frame at the top";
    //T.print (st_typing_to_string ty');
    let eq: st_equiv g c' c = r._3 in
    match ty' with
    | T_Frame _ _ c'' f tot ty' -> Mkdtuple3 c'' ty' f
    | _ -> fail g None "Did not find a frame at the top..."
  )

let modify_type_derivation () = true

let rec list_as_vprop_typed g (l: list (a: atom & tot_typing g a tm_vprop)):
  t:term & tot_typing g t tm_vprop
= match l with
| [] -> (| tm_emp, emp_typing #g |)
| (| t, ty |) :: q -> 
let (| qt, qty |) = list_as_vprop_typed g q in
(| tm_star t qt, star_typing ty qty |)

//val list_as_vprop (vps:list term)
//  : term

#pop-options
#push-options "--z3rlimit 20"
let check_par
  (allow_inst:bool)
  (g:env)
  (t:st_term{Tm_Par? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check':bool -> check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  (
    let g = push_context "check_par" t.range g in
    let Tm_Par {pre1=preL; body1=eL; post1=postL; pre2=preR; body2=eR; post2=postR} = t.term in
    // Step 1: Type left branch in full context
    // The postcondition hint might be misleading, so we ignore it (for the moment; TODO: Can be used in both approaches)
    let (| eL_t, cL_t, eL_typing_t |) = check' allow_inst g eL pre pre_typing None in
    // Step 2: Find the common frame:
    let ty = simplify_st_typing eL_typing_t in
    // need to collect the tot_typing...
    let (| frames, typing_frame |) = collect_frames ty in
    let inter_list = compute_intersection_list g frames typing_frame in
    let (| inter, inter_typed |) = list_as_vprop_typed g inter_list in
    //let inter_typed: Ghost.erased (tot_typing g inter tm_vprop) = magic() in
    // inter is list of atoms
    // bind: cL, eL_typing, new_preR
    let (| eL, cL, eL_typing, new_preR |) 
      : (eL:st_term & c:comp & typing:st_typing g eL c & vprop)
    =
    // START APPROACH 1: We modify the type derivation (avoids retypechecking)
    (if modify_type_derivation () then
      let r = get_typing_deriv_and_frame (extract_common_frame inter_typed ty) in
      (| eL_t, r._1, r._2, r._3 |)
      //let (| cL, eL_typing, new_preR |) = r in
      //(| eL, cL, eL_typing, new_preR |)
    // END APPROACH 1
    // START APPROACH 2: We find the new left and right preconditions, and simply retypecheck
    else
      let (| new_preL, _, _ |) = remove_from_vprop inter pre_typing in
      let new_preR = inter in // from_list_to_term preR.range inter in
      let (| preL, preL_typing |) = check_term_with_expected_type g new_preL tm_vprop in
      let postL_hint = (if Tm_Unknown? postL.t then None else Some (intro_post_hint g None postL)) in
      let (| eL, cL, eL_typing |) = check' allow_inst g eL preL (E preL_typing) postL_hint in
      (| eL, cL, eL_typing, new_preR |) )
    // END APPROACH 2
  in
  let (| preR, preR_typing |) =
    check_term_with_expected_type g new_preR tm_vprop in
  if C_ST? cL
  then
    let cL_typing = MT.st_typing_correctness eL_typing in
    let postR_hint = (if Tm_Unknown? postR.t then None else Some (intro_post_hint g None postR)) in
    let (| eR, cR, eR_typing |) =
      check' allow_inst g eR preR (E preR_typing) postR_hint in

    if C_ST? cR && eq_univ (comp_u cL) (comp_u cR)
    then
      let cR_typing = MT.st_typing_correctness eR_typing in
      let x = fresh g in
      let d = T_Par _ _ _ _ _ x cL_typing cR_typing eL_typing eR_typing in
      match (try_frame_pre pre_typing d) with
      //match (repack (try_frame_pre pre_typing d) post_hint) with
      | Inl x -> repack x post_hint
      | _ -> fail g None "Failure in main function..."
    else fail g (Some eR.range) "par: cR is not stt"
  else fail g (Some eL.range) "par: cL is not stt"
  )
#pop-options