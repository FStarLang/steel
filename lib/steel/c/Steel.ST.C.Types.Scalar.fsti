module Steel.ST.C.Types.Scalar
open Steel.ST.Util
include Steel.ST.C.Types.Base

module P = Steel.FractionalPermission

// To be extracted as: t
[@@noextract_to "krml"] // primitive
val scalar_t ( [@@@strictly_positive] t: Type0) : Type0
[@@noextract_to "krml"] // proof-only
val scalar (t: Type) : typedef (scalar_t t)
val mk_scalar (#t: Type) (v: t) : Ghost (scalar_t t)
  (requires True)
  (ensures (fun y ->
    fractionable (scalar t) y /\
    full (scalar t) y
  ))

val mk_scalar_fractionable
  (#t: Type)
  (v: t)
  (p: P.perm)
: Lemma
  (requires (fractionable (scalar t) (mk_fraction (scalar t) (mk_scalar v) p)))
  (ensures (p `P.lesser_equal_perm` P.full_perm))

val mk_scalar_inj
  (#t: Type)
  (v1 v2: t)
  (p1 p2: P.perm)
: Lemma
  (requires (mk_fraction (scalar t) (mk_scalar v1) p1 == mk_fraction (scalar t) (mk_scalar v2) p2))
  (ensures (v1 == v2 /\ p1 == p2))
  [SMTPat [mk_fraction (scalar t) (mk_scalar v1) p1; mk_fraction (scalar t) (mk_scalar v2) p2]]

let scalar_unique
  (#opened: _)
  (#t: Type)
  (v1 v2: t)
  (p1 p2: P.perm)
  (r: ref (scalar t))
: STGhost unit opened
    (pts_to r (mk_fraction (scalar t) (mk_scalar v1) p1) `star` pts_to r (mk_fraction (scalar t) (mk_scalar v2) p2))
    (fun _ -> pts_to r (mk_fraction (scalar t) (mk_scalar v1) p1) `star` pts_to r (mk_fraction (scalar t) (mk_scalar v2) p2))
    (True)
    (fun _ -> v1 == v2 /\ (p1 `P.sum_perm` p2) `P.lesser_equal_perm` P.full_perm)
= noop ();
  fractional_permissions_theorem (mk_scalar v1) (mk_scalar v2) p1 p2 r;
  mk_scalar_inj v1 v2 P.full_perm P.full_perm

[@@noextract_to "krml"] // primitive
val read0 (#t: Type) (#v: Ghost.erased t) (#p: P.perm) (r: ref (scalar t)) : ST t
  (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p))
  (fun _ -> pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p))
  (True)
  (fun v' -> v' == Ghost.reveal v)

let mk_fraction_full_scalar (#t: Type) (v: t) : Lemma
  (mk_scalar v == mk_fraction (scalar t) (mk_scalar v) P.full_perm)
  [SMTPat (mk_scalar v)]
= ()

val get_scalar_value
  (#t: Type)
  (c: scalar_t t)
: GTot (option t)

val get_scalar_value_mk_fraction
  (#t: Type)
  (c: scalar_t t)
  (p: perm)
: Lemma
  (requires (fractionable (scalar t) c))
  (ensures (get_scalar_value (mk_fraction (scalar t) c p) == get_scalar_value c))
  [SMTPat (get_scalar_value (mk_fraction (scalar t) c p))]

val get_scalar_value_mk_scalar
  (#t: Type)
  (c: t)
: Lemma
  (get_scalar_value (mk_scalar c) == Some c)
  [SMTPat (get_scalar_value (mk_scalar c))]

val get_scalar_value_uninitialized
  (t: Type)
: Lemma
  (get_scalar_value (uninitialized (scalar t)) == None)
  [SMTPat (get_scalar_value (uninitialized (scalar t)))]

val get_scalar_value_unknown
  (t: Type)
: Lemma
  (get_scalar_value (unknown (scalar t)) == None)
  [SMTPat (get_scalar_value (unknown (scalar t)))]

val get_scalar_value_some
  (#t: Type)
  (c: scalar_t t)
: Lemma
  (requires (Some? (get_scalar_value c)))
  (ensures (
    exists v0 p . Ghost.reveal c == mk_fraction (scalar t) (mk_scalar v0) p
  ))
  [SMTPat (get_scalar_value c)]

inline_for_extraction [@@noextract_to "krml"]
let read (#t: Type) (#v: Ghost.erased (scalar_t t)) (r: ref (scalar t)) : ST t
  (pts_to r v)
  (fun _ -> pts_to r v)
  (exists v0 p . Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0) p)
  (fun v1 -> forall v0 p . (* {:pattern (mk_fraction (scalar t) (mk_scalar v0) p)} *) Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0) p ==> v0 == v1)
= let v0 = FStar.IndefiniteDescription.indefinite_description_tot _ (fun v0 -> exists p . Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0) p) in
  let p = FStar.IndefiniteDescription.indefinite_description_tot _ (fun p -> Ghost.reveal v == mk_fraction (scalar t) (mk_scalar (Ghost.reveal v0)) p) in
  introduce forall v0' p'.
      Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0') p' ==>
      v0' == Ghost.reveal v0 /\ p' == Ghost.reveal p with
    introduce _ ==> _ with _.
    mk_scalar_inj (Ghost.reveal v0) v0' p p';
  rewrite (pts_to _ _) (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v0)) p));
  let v1 = read0 r in
  rewrite (pts_to _ _) (pts_to r v);
  return v1

[@@noextract_to "krml"] // primitive
val write (#t: Type) (#v: Ghost.erased (scalar_t t)) (r: ref (scalar t)) (v': t) : ST unit
  (pts_to r v)
  (fun _ -> pts_to r (mk_fraction (scalar t) (mk_scalar v') P.full_perm))
  (full (scalar t) v)
  (fun _ -> True)
