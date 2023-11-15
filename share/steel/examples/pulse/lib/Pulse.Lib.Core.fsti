module Pulse.Lib.Core
open FStar.Ghost
open Steel.FractionalPermission
module U32 = FStar.UInt32
module G = FStar.Ghost
module Set = FStar.Set

(* Common alias *)
let one_half =
  half_perm full_perm

val double_one_half (_:unit)
  : Lemma (sum_perm one_half one_half == full_perm)

(* This attribute can be used on the indexes of a vprop
   to instruct the checker to call the SMT solver to relate
   occurrences of that index.

   For example, if you have

     val pts_to (x:ref a) ([@@@equate_by_smt] v:a) : vprop

   Then `pts_to x (a + b)` and `pts_to x (b + a)` will be
   matched by the prover by emitting an SMT query (a + b) == (b + a). Of course, 
   `pts_to x a` and `pts_to x a` will be matched purely by unification without
   emitted a trivial SMT query (a == a).

   By default, if none of the indexes of a vprop are marked with "equate_by_smt", 
   the _last_ argument of a vprop is considered to be equated by SMT. This makes 
   it convenient to write vprops like the one below, without paying special
   heed to this attribute.
  
     val pts_to (x:ref a) (v:a) : vprop
*)
val equate_by_smt : unit
(***** begin vprop_equiv *****)

#set-options "--print_implicits --ugly --print_universes"

[@@erasable]
val vprop : Type u#2

val emp : vprop
val ( ** ) (p q:vprop) : vprop
val pure (p:prop) : vprop
val exists_ (#a:Type) (p:a -> vprop) : vprop

val vprop_equiv (p q:vprop) : prop
val vprop_post_equiv (#t:Type u#a) (p q: t -> vprop) : prop

val intro_vprop_post_equiv
       (#t:Type u#a) 
       (p q: t -> vprop)
       (pf: (x:t -> vprop_equiv (p x) (q x)))
  : vprop_post_equiv p q

val elim_vprop_post_equiv (#t:Type u#a)
                          (p q: t -> vprop) 
                          (pf:vprop_post_equiv p q)
                          (x:t) 
    : vprop_equiv (p x) (q x)

val vprop_equiv_refl (v0:vprop) : vprop_equiv v0 v0

val vprop_equiv_sym (v0 v1:vprop) (_:vprop_equiv v0 v1)
  : vprop_equiv v1 v0

val vprop_equiv_trans (v0 v1 v2:vprop) (_:vprop_equiv v0 v1) (_:vprop_equiv v1 v2)
  : vprop_equiv v0 v2

val vprop_equiv_unit (x:vprop) : vprop_equiv (emp ** x) x

val vprop_equiv_comm (p1 p2:vprop)
  : vprop_equiv (p1 ** p2) (p2 ** p1)

val vprop_equiv_assoc (p1 p2 p3:vprop)
  : vprop_equiv (p1 ** p2 ** p3) (p1 ** (p2 ** p3))

val vprop_equiv_cong (p1 p2 p3 p4:vprop)
                     (_: vprop_equiv p1 p3)
                     (_: vprop_equiv p2 p4)
  : vprop_equiv (p1 ** p2) (p3 ** p4)

val vprop_equiv_ext (p1 p2:vprop) (_:p1 == p2)
  : vprop_equiv p1 p2

(***** end vprop_equiv *****)

(***** begin computation types and combinators *****)
val iname : eqtype
let inames = erased (FStar.Set.set iname)
let emp_inames : inames = Ghost.hide Set.empty

let join_inames (is1 is2 : inames) : inames =
  Set.union is1 is2

let inames_subset (is1 is2 : inames) : Type0 =
  Set.subset is1 is2

let (/!) (is1 is2 : inames) : Type0 =
  Set.disjoint is1 is2

val inv (p:vprop) : Type u#0

(* NB: Using EXACTLY the definitions of Steel.Effect.Common otherwise
we run into tons of pain when trying to define the operations. *)
val name_of_inv #p (i : inv p) : GTot iname

let mem_iname (e:inames) (i:iname) : erased bool = elift2 (fun e i -> Set.mem i e) e i
let mem_inv (#p:vprop) (e:inames) (i:inv p) : erased bool = mem_iname e (name_of_inv i)

let add_iname (e:inames) (i:iname) : inames = Set.union (Set.singleton i) (reveal e)
let add_inv (#p:vprop) (e:inames) (i:inv p) : inames = add_iname e (name_of_inv i)

(* Useful for reasoning about inames equalities. TODO: We need a decent
set of patterns. *)
val add_already_there #p (i : inv p) (is : inames)
  : Lemma (requires Set.mem (name_of_inv i) is)
          (ensures add_inv is i == is)
          [SMTPat (add_inv is i)]

(* stt a pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   may loop forever
   but if it returns, it returns `x:a`
   such that the final state satisfies `post x` *)
[@@extract_as_impure_effect]
val stt (a:Type u#a) (pre:vprop) (post:a -> vprop) : Type0

(* stt_unobservable a opens pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes an unobservable atomic step
   potentially opening invariants in `opens`
   and returns `x:a`
   such that the final state satisfies `post x` *)
[@@extract_as_impure_effect]
val stt_unobservable (a:Type u#a) (opens:inames) (pre:vprop) (post:a -> vprop) : Type u#(max 2 a)

(* stt_atomic a opens pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes a single concrete atomic step
   potentially opening invariants in `opens`
   and returns `x:a`
   such that the final state satisfies `post x` *)
[@@extract_as_impure_effect]
val stt_atomic (a:Type u#a) (opens:inames) (pre:vprop) (post:a -> vprop) : Type u#(max 2 a)

(* stt_ghost a opens pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes a single ghost atomic step (i.e. a step that does not modify the heap, and does not get extracted)
   potentially opening invariants in `opens`
   and returns `x:a`
   such that the final state satisfies `post x` *)
[@@ erasable]
//inline_for_extraction
val stt_ghost (a:Type u#a) (opens:inames) (pre:vprop) (post:a -> vprop) : Type u#(max 2 a)

//
// the returns should probably move to atomic,
//   once we have support for bind etc.
//

inline_for_extraction
val return_stt (#a:Type u#a) (x:a) (p:a -> vprop)
  : stt a (p x) (fun r -> p r ** pure (r == x))

inline_for_extraction
val return (#a:Type u#a) (x:a) (p:a -> vprop)
  : stt a (p x) p

inline_for_extraction
val return_stt_ghost (#a:Type u#a) (x:a) (p:a -> vprop)
  : stt_ghost a emp_inames (p x) (fun r -> p r ** pure (r == x))

inline_for_extraction
val return_stt_ghost_noeq (#a:Type u#a) (x:a) (p:a -> vprop)
  : stt_ghost a emp_inames (p x) p

// Return in ghost?

inline_for_extraction
val bind_stt
  (#a:Type u#a) (#b:Type u#b)
  (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt a pre1 post1)
  (e2:(x:a -> stt b (post1 x) post2))
  : stt b pre1 post2

inline_for_extraction
val lift_stt_atomic (#a:Type u#a) (#opens:inames) (#pre:vprop) (#post:a -> vprop)
  (e:stt_atomic a opens pre post)
  : stt a pre post

inline_for_extraction
val bind_sttg
  (#a:Type u#a) (#b:Type u#b)
  (#opens:inames)
  (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt_ghost a opens pre1 post1)
  (e2:(x:a -> stt_ghost b opens (post1 x) post2))
  : stt_ghost b opens pre1 post2

type non_informative_witness (a:Type u#a) =
  x:Ghost.erased a -> y:a{y == Ghost.reveal x}

inline_for_extraction
val bind_stt_atomic_ghost
  (#a:Type u#a) (#b:Type u#b)
  (#opens:inames)
  (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt_atomic a opens pre1 post1)
  (e2:(x:a -> stt_ghost b opens (post1 x) post2))
  (reveal_b:non_informative_witness b)
  : stt_atomic b opens pre1 post2

inline_for_extraction
val bind_stt_ghost_atomic
  (#a:Type u#a) (#b:Type u#b)
  (#opens:inames)
  (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt_ghost a opens pre1 post1)
  (e2:(x:a -> stt_atomic b opens (post1 x) post2))
  (reveal_a:non_informative_witness a)
  : stt_atomic b opens pre1 post2

inline_for_extraction
val lift_stt_ghost (#a:Type u#a) (#opens:inames) (#pre:vprop) (#post:a -> vprop)
  (e:stt_ghost a opens pre post)
  (reveal_a:(x:Ghost.erased a -> y:a{y == Ghost.reveal x}))
  : stt_atomic a opens pre post

inline_for_extraction
val frame_stt
  (#a:Type u#a)
  (#pre:vprop) (#post:a -> vprop)
  (frame:vprop)
  (e:stt a pre post)
  : stt a (pre ** frame) (fun x -> post x ** frame)

inline_for_extraction
val frame_stt_atomic
  (#a:Type u#a)
  (#opens:inames)
  (#pre:vprop) (#post:a -> vprop)
  (frame:vprop)
  (e:stt_atomic a opens pre post)
  : stt_atomic a opens (pre ** frame) (fun x -> post x ** frame)

inline_for_extraction
val frame_stt_ghost
  (#a:Type u#a)
  (#opens:inames)
  (#pre:vprop) (#post:a -> vprop)
  (frame:vprop)
  (e:stt_ghost a opens pre post)
  : stt_ghost a opens (pre ** frame) (fun x -> post x ** frame)

inline_for_extraction
val sub_stt (#a:Type u#a)
            (#pre1:vprop)
            (pre2:vprop)
            (#post1:a -> vprop)
            (post2:a -> vprop)
            (pf1 : vprop_equiv pre1 pre2)
            (pf2 : vprop_post_equiv post1 post2)
            (e:stt a pre1 post1)
  : stt a pre2 post2

inline_for_extraction
val sub_stt_atomic
  (#a:Type u#a)
  (#opens:inames)
  (#pre1:vprop)
  (pre2:vprop)
  (#post1:a -> vprop)
  (post2:a -> vprop)
  (pf1 : vprop_equiv pre1 pre2)
  (pf2 : vprop_post_equiv post1 post2)
  (e:stt_atomic a opens pre1 post1)
  : stt_atomic a opens pre2 post2

inline_for_extraction
val sub_invs_stt_atomic
  (#a:Type u#a)
  (#opens1 #opens2:inames)
  (#pre:vprop)
  (#post:a -> vprop)
  (e:stt_atomic a opens1 pre post)
  (_ : squash (inames_subset opens1 opens2))
  : stt_atomic a opens2 pre post

inline_for_extraction
val sub_stt_ghost
  (#a:Type u#a)
  (#opens:inames)
  (#pre1:vprop)
  (pre2:vprop)
  (#post1:a -> vprop)
  (post2:a -> vprop)
  (pf1 : vprop_equiv pre1 pre2)
  (pf2 : vprop_post_equiv post1 post2)
  (e:stt_ghost a opens pre1 post1)
  : stt_ghost a opens pre2 post2

inline_for_extraction
val sub_invs_stt_ghost
  (#a:Type u#a)
  (#opens1 #opens2:inames)
  (#pre:vprop)
  (#post:a -> vprop)
  (e:stt_ghost a opens1 pre post)
  (_ : squash (inames_subset opens1 opens2))
  : stt_ghost a opens2 pre post

inline_for_extraction
val return_stt_unobservable (#a:Type u#a) (x:a) (p:a -> vprop)
  : stt_unobservable a emp_inames (p x) (fun r -> p r ** pure (r == x))

inline_for_extraction
val return_stt_unobservable_noeq (#a:Type u#a) (x:a) (p:a -> vprop)
  : stt_unobservable a emp_inames (p x) p

inline_for_extraction
val new_invariant (p:vprop) : stt_unobservable (inv p) emp_inames p (fun _ -> emp)

inline_for_extraction
val new_invariant' (p:vprop) : stt_atomic (inv p) emp_inames p (fun _ -> emp)

inline_for_extraction
val with_invariant_g (#a:Type)
                   (#fp:vprop)
                   (#fp':erased a -> vprop)
                   (#f_opens:inames)
                   (#p:vprop)
                   (i:inv p{not (mem_inv f_opens i)})
                   ($f:unit -> stt_ghost a f_opens
                                            (p ** fp)
                                            (fun x -> p ** fp' x))
  : stt_unobservable (erased a) (add_inv f_opens i) fp fp'

inline_for_extraction
val with_invariant_a (#a:Type)
                   (#fp:vprop)
                   (#fp':a -> vprop)
                   (#opened_invariants:inames)
                   (#p:vprop)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   ($f:unit -> stt_atomic a (add_inv opened_invariants i) 
                                            (p ** fp)
                                            (fun x -> p ** fp' x))
  : stt_atomic a opened_invariants fp fp'

inline_for_extraction
let unit_non_informative : non_informative_witness unit =
  fun u -> u

inline_for_extraction
let prop_non_informative : non_informative_witness prop =
  fun p -> p

inline_for_extraction
let erased_non_informative (a:Type u#a) : non_informative_witness (Ghost.erased u#a a) =
  fun x -> Ghost.reveal x

inline_for_extraction
let squash_non_informative (a:Type u#a) : non_informative_witness (squash  u#a a) =
  fun x -> x

(***** end computation types and combinators *****)

val rewrite (p:vprop) (q:vprop) (_:vprop_equiv p q)
  : stt_ghost unit emp_inames p (fun _ -> q)


open FStar.Ghost

val elim_pure_explicit (p:prop)
  : stt_ghost (squash p) emp_inames
              (pure p)
              (fun _ -> emp)

val elim_pure (_:unit) (#p:prop)
  : stt_ghost (squash p) emp_inames
              (pure p)
              (fun _ -> emp)

val intro_pure (p:prop) (_:squash p)
  : stt_ghost unit emp_inames
              emp
              (fun _ -> pure p)

val elim_exists (#a:Type) (p:a -> vprop)
  : stt_ghost (erased a) emp_inames (exists_ p) (fun x -> p (reveal x))

val intro_exists (#a:Type) (p:a -> vprop) (e:a)
  : stt_ghost unit emp_inames (p e) (fun _ -> exists_ p)

val intro_exists_erased (#a:Type) (p:a -> vprop) (e:erased a)
  : stt_ghost unit emp_inames (p (reveal e)) (fun _ -> exists_ p)

val while_loop
  (inv:bool -> vprop)
  (cond:stt bool (exists_ inv) inv)
  (body:stt unit (inv true) (fun _ -> exists_ inv))
  : stt unit (exists_ inv) (fun _ -> inv false)

val stt_ghost_reveal (a:Type) (x:erased a)
  : stt_ghost a emp_inames emp (fun y -> pure (reveal x == y))

val stt_admit (a:Type) (p:vprop) (q:a -> vprop) : stt a p q
val stt_atomic_admit (a:Type) (p:vprop) (q:a -> vprop) : stt_atomic a emp_inames p q
val stt_ghost_admit (a:Type) (p:vprop) (q:a -> vprop) : stt_ghost a emp_inames p q

val stt_par
  (#aL:Type u#a)
  (#aR:Type u#a)
  (#preL:vprop)
  (#postL:aL -> vprop) 
  (#preR:vprop)
  (#postR:aR -> vprop)
  (f:stt aL preL postL)
  (g:stt aR preR postR)
  : stt (aL & aR)
        (preL ** preR)
        (fun x -> postL (fst x) ** postR (snd x))


val assert_ (p:vprop)
  : stt_ghost unit emp_inames p (fun _ -> p)


val assume_ (p:vprop)
  : stt_ghost unit emp_inames emp (fun _ -> p)

val drop_ (p:vprop) 
  : stt_ghost unit emp_inames p (fun _ -> emp)

val elim_false (a:Type) (p:a -> vprop)
  : stt_ghost a emp_inames (pure False) p

let eq2_prop (#a:Type) (x:a) (y:a) : prop = x == y
