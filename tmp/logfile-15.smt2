(get-info :version)
; (:version "4.8.7")
; Started: 2023-08-11 09:00:50
; Silicon.version: 1.1-SNAPSHOT (7f2e6823@(detached))
; Input file: <unknown>
; Verifier id: 00
; ------------------------------------------------------------
; Begin preamble
; ////////// Static preamble
; 
; ; /z3config.smt2
(set-option :print-success true) ; Boogie: false
(set-option :global-decls true) ; Boogie: default
(set-option :auto_config false) ; Usually a good idea
(set-option :smt.restart_strategy 0)
(set-option :smt.restart_factor |1.5|)
(set-option :smt.case_split 3)
(set-option :smt.delay_units true)
(set-option :smt.delay_units_threshold 16)
(set-option :nnf.sk_hack true)
(set-option :type_check true)
(set-option :smt.bv.reflect true)
(set-option :smt.mbqi false)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :smt.qi.max_multi_patterns 1000)
(set-option :smt.phase_selection 0) ; default: 3, Boogie: 0
(set-option :sat.phase caching)
(set-option :sat.random_seed 0)
(set-option :nlsat.randomize true)
(set-option :nlsat.seed 0)
(set-option :nlsat.shuffle_vars false)
(set-option :fp.spacer.order_children 0) ; Not available with Z3 4.5
(set-option :fp.spacer.random_seed 0) ; Not available with Z3 4.5
(set-option :smt.arith.random_initial_value true) ; Boogie: true
(set-option :smt.random_seed 0)
(set-option :sls.random_offset true)
(set-option :sls.random_seed 0)
(set-option :sls.restart_init false)
(set-option :sls.walksat_ucb true)
(set-option :model.v2 true)
; 
; ; /preamble.smt2
(declare-datatypes (($Snap 0)) ((
    ($Snap.unit)
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
(declare-sort $Ref 0)
(declare-const $Ref.null $Ref)
(declare-sort $FPM 0)
(declare-sort $PPM 0)
(define-sort $Perm () Real)
(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)
(define-fun $Perm.isValidVar ((p $Perm)) Bool
	(<= $Perm.No p))
(define-fun $Perm.isReadVar ((p $Perm)) Bool
    (and ($Perm.isValidVar p)
         (not (= p $Perm.No))))
(define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))
(define-fun $Math.min ((a Int) (b Int)) Int
    (ite (<= a b) a b))
(define-fun $Math.clip ((a Int)) Int
    (ite (< a 0) 0 a))
; ////////// Sorts
(declare-sort Set<Int> 0)
(declare-sort Set<$Ref> 0)
(declare-sort Set<$Snap> 0)
(declare-sort IArray 0)
(declare-sort $FVF<val> 0)
; ////////// Sort wrappers
; Declaring additional sort wrappers
(declare-fun $SortWrappers.IntTo$Snap (Int) $Snap)
(declare-fun $SortWrappers.$SnapToInt ($Snap) Int)
(assert (forall ((x Int)) (!
    (= x ($SortWrappers.$SnapToInt($SortWrappers.IntTo$Snap x)))
    :pattern (($SortWrappers.IntTo$Snap x))
    :qid |$Snap.$SnapToIntTo$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.IntTo$Snap($SortWrappers.$SnapToInt x)))
    :pattern (($SortWrappers.$SnapToInt x))
    :qid |$Snap.IntTo$SnapToInt|
    )))
(declare-fun $SortWrappers.BoolTo$Snap (Bool) $Snap)
(declare-fun $SortWrappers.$SnapToBool ($Snap) Bool)
(assert (forall ((x Bool)) (!
    (= x ($SortWrappers.$SnapToBool($SortWrappers.BoolTo$Snap x)))
    :pattern (($SortWrappers.BoolTo$Snap x))
    :qid |$Snap.$SnapToBoolTo$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.BoolTo$Snap($SortWrappers.$SnapToBool x)))
    :pattern (($SortWrappers.$SnapToBool x))
    :qid |$Snap.BoolTo$SnapToBool|
    )))
(declare-fun $SortWrappers.$RefTo$Snap ($Ref) $Snap)
(declare-fun $SortWrappers.$SnapTo$Ref ($Snap) $Ref)
(assert (forall ((x $Ref)) (!
    (= x ($SortWrappers.$SnapTo$Ref($SortWrappers.$RefTo$Snap x)))
    :pattern (($SortWrappers.$RefTo$Snap x))
    :qid |$Snap.$SnapTo$RefTo$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.$RefTo$Snap($SortWrappers.$SnapTo$Ref x)))
    :pattern (($SortWrappers.$SnapTo$Ref x))
    :qid |$Snap.$RefTo$SnapTo$Ref|
    )))
(declare-fun $SortWrappers.$PermTo$Snap ($Perm) $Snap)
(declare-fun $SortWrappers.$SnapTo$Perm ($Snap) $Perm)
(assert (forall ((x $Perm)) (!
    (= x ($SortWrappers.$SnapTo$Perm($SortWrappers.$PermTo$Snap x)))
    :pattern (($SortWrappers.$PermTo$Snap x))
    :qid |$Snap.$SnapTo$PermTo$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.$PermTo$Snap($SortWrappers.$SnapTo$Perm x)))
    :pattern (($SortWrappers.$SnapTo$Perm x))
    :qid |$Snap.$PermTo$SnapTo$Perm|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.Set<Int>To$Snap (Set<Int>) $Snap)
(declare-fun $SortWrappers.$SnapToSet<Int> ($Snap) Set<Int>)
(assert (forall ((x Set<Int>)) (!
    (= x ($SortWrappers.$SnapToSet<Int>($SortWrappers.Set<Int>To$Snap x)))
    :pattern (($SortWrappers.Set<Int>To$Snap x))
    :qid |$Snap.$SnapToSet<Int>To$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.Set<Int>To$Snap($SortWrappers.$SnapToSet<Int> x)))
    :pattern (($SortWrappers.$SnapToSet<Int> x))
    :qid |$Snap.Set<Int>To$SnapToSet<Int>|
    )))
(declare-fun $SortWrappers.Set<$Ref>To$Snap (Set<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapToSet<$Ref> ($Snap) Set<$Ref>)
(assert (forall ((x Set<$Ref>)) (!
    (= x ($SortWrappers.$SnapToSet<$Ref>($SortWrappers.Set<$Ref>To$Snap x)))
    :pattern (($SortWrappers.Set<$Ref>To$Snap x))
    :qid |$Snap.$SnapToSet<$Ref>To$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.Set<$Ref>To$Snap($SortWrappers.$SnapToSet<$Ref> x)))
    :pattern (($SortWrappers.$SnapToSet<$Ref> x))
    :qid |$Snap.Set<$Ref>To$SnapToSet<$Ref>|
    )))
(declare-fun $SortWrappers.Set<$Snap>To$Snap (Set<$Snap>) $Snap)
(declare-fun $SortWrappers.$SnapToSet<$Snap> ($Snap) Set<$Snap>)
(assert (forall ((x Set<$Snap>)) (!
    (= x ($SortWrappers.$SnapToSet<$Snap>($SortWrappers.Set<$Snap>To$Snap x)))
    :pattern (($SortWrappers.Set<$Snap>To$Snap x))
    :qid |$Snap.$SnapToSet<$Snap>To$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.Set<$Snap>To$Snap($SortWrappers.$SnapToSet<$Snap> x)))
    :pattern (($SortWrappers.$SnapToSet<$Snap> x))
    :qid |$Snap.Set<$Snap>To$SnapToSet<$Snap>|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.IArrayTo$Snap (IArray) $Snap)
(declare-fun $SortWrappers.$SnapToIArray ($Snap) IArray)
(assert (forall ((x IArray)) (!
    (= x ($SortWrappers.$SnapToIArray($SortWrappers.IArrayTo$Snap x)))
    :pattern (($SortWrappers.IArrayTo$Snap x))
    :qid |$Snap.$SnapToIArrayTo$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.IArrayTo$Snap($SortWrappers.$SnapToIArray x)))
    :pattern (($SortWrappers.$SnapToIArray x))
    :qid |$Snap.IArrayTo$SnapToIArray|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$FVF<val>To$Snap ($FVF<val>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<val> ($Snap) $FVF<val>)
(assert (forall ((x $FVF<val>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<val>($SortWrappers.$FVF<val>To$Snap x)))
    :pattern (($SortWrappers.$FVF<val>To$Snap x))
    :qid |$Snap.$SnapTo$FVF<val>To$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.$FVF<val>To$Snap($SortWrappers.$SnapTo$FVF<val> x)))
    :pattern (($SortWrappers.$SnapTo$FVF<val> x))
    :qid |$Snap.$FVF<val>To$SnapTo$FVF<val>|
    )))
; ////////// Symbols
(declare-fun Set_in (Int Set<Int>) Bool)
(declare-fun Set_card (Set<Int>) Int)
(declare-const Set_empty Set<Int>)
(declare-fun Set_singleton (Int) Set<Int>)
(declare-fun Set_unionone (Set<Int> Int) Set<Int>)
(declare-fun Set_union (Set<Int> Set<Int>) Set<Int>)
(declare-fun Set_disjoint (Set<Int> Set<Int>) Bool)
(declare-fun Set_difference (Set<Int> Set<Int>) Set<Int>)
(declare-fun Set_intersection (Set<Int> Set<Int>) Set<Int>)
(declare-fun Set_subset (Set<Int> Set<Int>) Bool)
(declare-fun Set_equal (Set<Int> Set<Int>) Bool)
(declare-fun Set_in ($Ref Set<$Ref>) Bool)
(declare-fun Set_card (Set<$Ref>) Int)
(declare-const Set_empty Set<$Ref>)
(declare-fun Set_singleton ($Ref) Set<$Ref>)
(declare-fun Set_unionone (Set<$Ref> $Ref) Set<$Ref>)
(declare-fun Set_union (Set<$Ref> Set<$Ref>) Set<$Ref>)
(declare-fun Set_disjoint (Set<$Ref> Set<$Ref>) Bool)
(declare-fun Set_difference (Set<$Ref> Set<$Ref>) Set<$Ref>)
(declare-fun Set_intersection (Set<$Ref> Set<$Ref>) Set<$Ref>)
(declare-fun Set_subset (Set<$Ref> Set<$Ref>) Bool)
(declare-fun Set_equal (Set<$Ref> Set<$Ref>) Bool)
(declare-fun Set_in ($Snap Set<$Snap>) Bool)
(declare-fun Set_card (Set<$Snap>) Int)
(declare-const Set_empty Set<$Snap>)
(declare-fun Set_singleton ($Snap) Set<$Snap>)
(declare-fun Set_unionone (Set<$Snap> $Snap) Set<$Snap>)
(declare-fun Set_union (Set<$Snap> Set<$Snap>) Set<$Snap>)
(declare-fun Set_disjoint (Set<$Snap> Set<$Snap>) Bool)
(declare-fun Set_difference (Set<$Snap> Set<$Snap>) Set<$Snap>)
(declare-fun Set_intersection (Set<$Snap> Set<$Snap>) Set<$Snap>)
(declare-fun Set_subset (Set<$Snap> Set<$Snap>) Bool)
(declare-fun Set_equal (Set<$Snap> Set<$Snap>) Bool)
(declare-fun slot<Ref> (IArray Int) $Ref)
(declare-fun len<Int> (IArray) Int)
(declare-fun first<IArray> ($Ref) IArray)
(declare-fun second<Int> ($Ref) Int)
; /field_value_functions_declarations.smt2 [val: Int]
(declare-fun $FVF.domain_val ($FVF<val>) Set<$Ref>)
(declare-fun $FVF.lookup_val ($FVF<val> $Ref) Int)
(declare-fun $FVF.after_val ($FVF<val> $FVF<val>) Bool)
(declare-fun $FVF.loc_val (Int $Ref) Bool)
(declare-fun $FVF.perm_val ($FPM $Ref) $Perm)
(declare-const $fvfTOP_val $FVF<val>)
; Declaring symbols related to program functions (from program analysis)
; Snapshot variable to be used during function verification
(declare-fun s@$ () $Snap)
; Declaring predicate trigger functions
; ////////// Uniqueness assumptions from domains
; ////////// Axioms
(assert (forall ((s Set<Int>)) (!
  (<= 0 (Set_card s))
  :pattern ((Set_card s))
  :qid |$Set[Int]_prog.card_non_negative|)))
(assert (forall ((e Int)) (!
  (not (Set_in e (as Set_empty  Set<Int>)))
  :pattern ((Set_in e (as Set_empty  Set<Int>)))
  :qid |$Set[Int]_prog.in_empty_set|)))
(assert (forall ((s Set<Int>)) (!
  (and
    (= (= (Set_card s) 0) (= s (as Set_empty  Set<Int>)))
    (=>
      (not (= (Set_card s) 0))
      (exists ((e Int)) (!
        (Set_in e s)
        :pattern ((Set_in e s))
        ))))
  :pattern ((Set_card s))
  :qid |$Set[Int]_prog.empty_set_cardinality|)))
(assert (forall ((e Int)) (!
  (Set_in e (Set_singleton e))
  :pattern ((Set_singleton e))
  :qid |$Set[Int]_prog.in_singleton_set|)))
(assert (forall ((e1 Int) (e2 Int)) (!
  (= (Set_in e1 (Set_singleton e2)) (= e1 e2))
  :pattern ((Set_in e1 (Set_singleton e2)))
  :qid |$Set[Int]_prog.in_singleton_set_equality|)))
(assert (forall ((e Int)) (!
  (= (Set_card (Set_singleton e)) 1)
  :pattern ((Set_card (Set_singleton e)))
  :qid |$Set[Int]_prog.singleton_set_cardinality|)))
(assert (forall ((s Set<Int>) (e Int)) (!
  (Set_in e (Set_unionone s e))
  :pattern ((Set_unionone s e))
  :qid |$Set[Int]_prog.in_unionone_same|)))
(assert (forall ((s Set<Int>) (e1 Int) (e2 Int)) (!
  (= (Set_in e1 (Set_unionone s e2)) (or (= e1 e2) (Set_in e1 s)))
  :pattern ((Set_in e1 (Set_unionone s e2)))
  :qid |$Set[Int]_prog.in_unionone_other|)))
(assert (forall ((s Set<Int>) (e1 Int) (e2 Int)) (!
  (=> (Set_in e1 s) (Set_in e1 (Set_unionone s e2)))
  :pattern ((Set_in e1 s) (Set_unionone s e2))
  :qid |$Set[Int]_prog.invariance_in_unionone|)))
(assert (forall ((s Set<Int>) (e Int)) (!
  (=> (Set_in e s) (= (Set_card (Set_unionone s e)) (Set_card s)))
  :pattern ((Set_card (Set_unionone s e)))
  :qid |$Set[Int]_prog.unionone_cardinality_invariant|)))
(assert (forall ((s Set<Int>) (e Int)) (!
  (=> (not (Set_in e s)) (= (Set_card (Set_unionone s e)) (+ (Set_card s) 1)))
  :pattern ((Set_card (Set_unionone s e)))
  :qid |$Set[Int]_prog.unionone_cardinality_changed|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (= (Set_in e (Set_union s1 s2)) (or (Set_in e s1) (Set_in e s2)))
  :pattern ((Set_in e (Set_union s1 s2)))
  :qid |$Set[Int]_prog.in_union_in_one|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (=> (Set_in e s1) (Set_in e (Set_union s1 s2)))
  :pattern ((Set_in e s1) (Set_union s1 s2))
  :qid |$Set[Int]_prog.in_left_in_union|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (=> (Set_in e s2) (Set_in e (Set_union s1 s2)))
  :pattern ((Set_in e s2) (Set_union s1 s2))
  :qid |$Set[Int]_prog.in_right_in_union|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (= (Set_in e (Set_intersection s1 s2)) (and (Set_in e s1) (Set_in e s2)))
  :pattern ((Set_in e (Set_intersection s1 s2)))
  :pattern ((Set_intersection s1 s2) (Set_in e s1))
  :pattern ((Set_intersection s1 s2) (Set_in e s2))
  :qid |$Set[Int]_prog.in_intersection_in_both|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (= (Set_union s1 (Set_union s1 s2)) (Set_union s1 s2))
  :pattern ((Set_union s1 (Set_union s1 s2)))
  :qid |$Set[Int]_prog.union_left_idempotency|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (= (Set_union (Set_union s1 s2) s2) (Set_union s1 s2))
  :pattern ((Set_union (Set_union s1 s2) s2))
  :qid |$Set[Int]_prog.union_right_idempotency|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (= (Set_intersection s1 (Set_intersection s1 s2)) (Set_intersection s1 s2))
  :pattern ((Set_intersection s1 (Set_intersection s1 s2)))
  :qid |$Set[Int]_prog.intersection_left_idempotency|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (= (Set_intersection (Set_intersection s1 s2) s2) (Set_intersection s1 s2))
  :pattern ((Set_intersection (Set_intersection s1 s2) s2))
  :qid |$Set[Int]_prog.intersection_right_idempotency|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (=
    (+ (Set_card (Set_union s1 s2)) (Set_card (Set_intersection s1 s2)))
    (+ (Set_card s1) (Set_card s2)))
  :pattern ((Set_card (Set_union s1 s2)))
  :pattern ((Set_card (Set_intersection s1 s2)))
  :qid |$Set[Int]_prog.cardinality_sums|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (= (Set_in e (Set_difference s1 s2)) (and (Set_in e s1) (not (Set_in e s2))))
  :pattern ((Set_in e (Set_difference s1 s2)))
  :qid |$Set[Int]_prog.in_difference|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (=> (Set_in e s2) (not (Set_in e (Set_difference s1 s2))))
  :pattern ((Set_difference s1 s2) (Set_in e s2))
  :qid |$Set[Int]_prog.not_in_difference|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (=
    (Set_subset s1 s2)
    (forall ((e Int)) (!
      (=> (Set_in e s1) (Set_in e s2))
      :pattern ((Set_in e s1))
      :pattern ((Set_in e s2))
      )))
  :pattern ((Set_subset s1 s2))
  :qid |$Set[Int]_prog.subset_definition|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (=
    (Set_equal s1 s2)
    (forall ((e Int)) (!
      (= (Set_in e s1) (Set_in e s2))
      :pattern ((Set_in e s1))
      :pattern ((Set_in e s2))
      )))
  :pattern ((Set_equal s1 s2))
  :qid |$Set[Int]_prog.equality_definition|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (=> (Set_equal s1 s2) (= s1 s2))
  :pattern ((Set_equal s1 s2))
  :qid |$Set[Int]_prog.native_equality|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (=
    (Set_disjoint s1 s2)
    (forall ((e Int)) (!
      (or (not (Set_in e s1)) (not (Set_in e s2)))
      :pattern ((Set_in e s1))
      :pattern ((Set_in e s2))
      )))
  :pattern ((Set_disjoint s1 s2))
  :qid |$Set[Int]_prog.disjointness_definition|)))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (and
    (=
      (+
        (+ (Set_card (Set_difference s1 s2)) (Set_card (Set_difference s2 s1)))
        (Set_card (Set_intersection s1 s2)))
      (Set_card (Set_union s1 s2)))
    (=
      (Set_card (Set_difference s1 s2))
      (- (Set_card s1) (Set_card (Set_intersection s1 s2)))))
  :pattern ((Set_card (Set_difference s1 s2)))
  :qid |$Set[Int]_prog.cardinality_difference|)))
(assert (forall ((s Set<$Ref>)) (!
  (<= 0 (Set_card s))
  :pattern ((Set_card s))
  :qid |$Set[Ref]_prog.card_non_negative|)))
(assert (forall ((e $Ref)) (!
  (not (Set_in e (as Set_empty  Set<$Ref>)))
  :pattern ((Set_in e (as Set_empty  Set<$Ref>)))
  :qid |$Set[Ref]_prog.in_empty_set|)))
(assert (forall ((s Set<$Ref>)) (!
  (and
    (= (= (Set_card s) 0) (= s (as Set_empty  Set<$Ref>)))
    (=>
      (not (= (Set_card s) 0))
      (exists ((e $Ref)) (!
        (Set_in e s)
        :pattern ((Set_in e s))
        ))))
  :pattern ((Set_card s))
  :qid |$Set[Ref]_prog.empty_set_cardinality|)))
(assert (forall ((e $Ref)) (!
  (Set_in e (Set_singleton e))
  :pattern ((Set_singleton e))
  :qid |$Set[Ref]_prog.in_singleton_set|)))
(assert (forall ((e1 $Ref) (e2 $Ref)) (!
  (= (Set_in e1 (Set_singleton e2)) (= e1 e2))
  :pattern ((Set_in e1 (Set_singleton e2)))
  :qid |$Set[Ref]_prog.in_singleton_set_equality|)))
(assert (forall ((e $Ref)) (!
  (= (Set_card (Set_singleton e)) 1)
  :pattern ((Set_card (Set_singleton e)))
  :qid |$Set[Ref]_prog.singleton_set_cardinality|)))
(assert (forall ((s Set<$Ref>) (e $Ref)) (!
  (Set_in e (Set_unionone s e))
  :pattern ((Set_unionone s e))
  :qid |$Set[Ref]_prog.in_unionone_same|)))
(assert (forall ((s Set<$Ref>) (e1 $Ref) (e2 $Ref)) (!
  (= (Set_in e1 (Set_unionone s e2)) (or (= e1 e2) (Set_in e1 s)))
  :pattern ((Set_in e1 (Set_unionone s e2)))
  :qid |$Set[Ref]_prog.in_unionone_other|)))
(assert (forall ((s Set<$Ref>) (e1 $Ref) (e2 $Ref)) (!
  (=> (Set_in e1 s) (Set_in e1 (Set_unionone s e2)))
  :pattern ((Set_in e1 s) (Set_unionone s e2))
  :qid |$Set[Ref]_prog.invariance_in_unionone|)))
(assert (forall ((s Set<$Ref>) (e $Ref)) (!
  (=> (Set_in e s) (= (Set_card (Set_unionone s e)) (Set_card s)))
  :pattern ((Set_card (Set_unionone s e)))
  :qid |$Set[Ref]_prog.unionone_cardinality_invariant|)))
(assert (forall ((s Set<$Ref>) (e $Ref)) (!
  (=> (not (Set_in e s)) (= (Set_card (Set_unionone s e)) (+ (Set_card s) 1)))
  :pattern ((Set_card (Set_unionone s e)))
  :qid |$Set[Ref]_prog.unionone_cardinality_changed|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (= (Set_in e (Set_union s1 s2)) (or (Set_in e s1) (Set_in e s2)))
  :pattern ((Set_in e (Set_union s1 s2)))
  :qid |$Set[Ref]_prog.in_union_in_one|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (=> (Set_in e s1) (Set_in e (Set_union s1 s2)))
  :pattern ((Set_in e s1) (Set_union s1 s2))
  :qid |$Set[Ref]_prog.in_left_in_union|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (=> (Set_in e s2) (Set_in e (Set_union s1 s2)))
  :pattern ((Set_in e s2) (Set_union s1 s2))
  :qid |$Set[Ref]_prog.in_right_in_union|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (= (Set_in e (Set_intersection s1 s2)) (and (Set_in e s1) (Set_in e s2)))
  :pattern ((Set_in e (Set_intersection s1 s2)))
  :pattern ((Set_intersection s1 s2) (Set_in e s1))
  :pattern ((Set_intersection s1 s2) (Set_in e s2))
  :qid |$Set[Ref]_prog.in_intersection_in_both|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (= (Set_union s1 (Set_union s1 s2)) (Set_union s1 s2))
  :pattern ((Set_union s1 (Set_union s1 s2)))
  :qid |$Set[Ref]_prog.union_left_idempotency|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (= (Set_union (Set_union s1 s2) s2) (Set_union s1 s2))
  :pattern ((Set_union (Set_union s1 s2) s2))
  :qid |$Set[Ref]_prog.union_right_idempotency|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (= (Set_intersection s1 (Set_intersection s1 s2)) (Set_intersection s1 s2))
  :pattern ((Set_intersection s1 (Set_intersection s1 s2)))
  :qid |$Set[Ref]_prog.intersection_left_idempotency|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (= (Set_intersection (Set_intersection s1 s2) s2) (Set_intersection s1 s2))
  :pattern ((Set_intersection (Set_intersection s1 s2) s2))
  :qid |$Set[Ref]_prog.intersection_right_idempotency|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (=
    (+ (Set_card (Set_union s1 s2)) (Set_card (Set_intersection s1 s2)))
    (+ (Set_card s1) (Set_card s2)))
  :pattern ((Set_card (Set_union s1 s2)))
  :pattern ((Set_card (Set_intersection s1 s2)))
  :qid |$Set[Ref]_prog.cardinality_sums|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (= (Set_in e (Set_difference s1 s2)) (and (Set_in e s1) (not (Set_in e s2))))
  :pattern ((Set_in e (Set_difference s1 s2)))
  :qid |$Set[Ref]_prog.in_difference|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (=> (Set_in e s2) (not (Set_in e (Set_difference s1 s2))))
  :pattern ((Set_difference s1 s2) (Set_in e s2))
  :qid |$Set[Ref]_prog.not_in_difference|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (=
    (Set_subset s1 s2)
    (forall ((e $Ref)) (!
      (=> (Set_in e s1) (Set_in e s2))
      :pattern ((Set_in e s1))
      :pattern ((Set_in e s2))
      )))
  :pattern ((Set_subset s1 s2))
  :qid |$Set[Ref]_prog.subset_definition|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (=
    (Set_equal s1 s2)
    (forall ((e $Ref)) (!
      (= (Set_in e s1) (Set_in e s2))
      :pattern ((Set_in e s1))
      :pattern ((Set_in e s2))
      )))
  :pattern ((Set_equal s1 s2))
  :qid |$Set[Ref]_prog.equality_definition|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (=> (Set_equal s1 s2) (= s1 s2))
  :pattern ((Set_equal s1 s2))
  :qid |$Set[Ref]_prog.native_equality|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (=
    (Set_disjoint s1 s2)
    (forall ((e $Ref)) (!
      (or (not (Set_in e s1)) (not (Set_in e s2)))
      :pattern ((Set_in e s1))
      :pattern ((Set_in e s2))
      )))
  :pattern ((Set_disjoint s1 s2))
  :qid |$Set[Ref]_prog.disjointness_definition|)))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (and
    (=
      (+
        (+ (Set_card (Set_difference s1 s2)) (Set_card (Set_difference s2 s1)))
        (Set_card (Set_intersection s1 s2)))
      (Set_card (Set_union s1 s2)))
    (=
      (Set_card (Set_difference s1 s2))
      (- (Set_card s1) (Set_card (Set_intersection s1 s2)))))
  :pattern ((Set_card (Set_difference s1 s2)))
  :qid |$Set[Ref]_prog.cardinality_difference|)))
(assert (forall ((s Set<$Snap>)) (!
  (<= 0 (Set_card s))
  :pattern ((Set_card s))
  :qid |$Set[Snap]_prog.card_non_negative|)))
(assert (forall ((e $Snap)) (!
  (not (Set_in e (as Set_empty  Set<$Snap>)))
  :pattern ((Set_in e (as Set_empty  Set<$Snap>)))
  :qid |$Set[Snap]_prog.in_empty_set|)))
(assert (forall ((s Set<$Snap>)) (!
  (and
    (= (= (Set_card s) 0) (= s (as Set_empty  Set<$Snap>)))
    (=>
      (not (= (Set_card s) 0))
      (exists ((e $Snap)) (!
        (Set_in e s)
        :pattern ((Set_in e s))
        ))))
  :pattern ((Set_card s))
  :qid |$Set[Snap]_prog.empty_set_cardinality|)))
(assert (forall ((e $Snap)) (!
  (Set_in e (Set_singleton e))
  :pattern ((Set_singleton e))
  :qid |$Set[Snap]_prog.in_singleton_set|)))
(assert (forall ((e1 $Snap) (e2 $Snap)) (!
  (= (Set_in e1 (Set_singleton e2)) (= e1 e2))
  :pattern ((Set_in e1 (Set_singleton e2)))
  :qid |$Set[Snap]_prog.in_singleton_set_equality|)))
(assert (forall ((e $Snap)) (!
  (= (Set_card (Set_singleton e)) 1)
  :pattern ((Set_card (Set_singleton e)))
  :qid |$Set[Snap]_prog.singleton_set_cardinality|)))
(assert (forall ((s Set<$Snap>) (e $Snap)) (!
  (Set_in e (Set_unionone s e))
  :pattern ((Set_unionone s e))
  :qid |$Set[Snap]_prog.in_unionone_same|)))
(assert (forall ((s Set<$Snap>) (e1 $Snap) (e2 $Snap)) (!
  (= (Set_in e1 (Set_unionone s e2)) (or (= e1 e2) (Set_in e1 s)))
  :pattern ((Set_in e1 (Set_unionone s e2)))
  :qid |$Set[Snap]_prog.in_unionone_other|)))
(assert (forall ((s Set<$Snap>) (e1 $Snap) (e2 $Snap)) (!
  (=> (Set_in e1 s) (Set_in e1 (Set_unionone s e2)))
  :pattern ((Set_in e1 s) (Set_unionone s e2))
  :qid |$Set[Snap]_prog.invariance_in_unionone|)))
(assert (forall ((s Set<$Snap>) (e $Snap)) (!
  (=> (Set_in e s) (= (Set_card (Set_unionone s e)) (Set_card s)))
  :pattern ((Set_card (Set_unionone s e)))
  :qid |$Set[Snap]_prog.unionone_cardinality_invariant|)))
(assert (forall ((s Set<$Snap>) (e $Snap)) (!
  (=> (not (Set_in e s)) (= (Set_card (Set_unionone s e)) (+ (Set_card s) 1)))
  :pattern ((Set_card (Set_unionone s e)))
  :qid |$Set[Snap]_prog.unionone_cardinality_changed|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>) (e $Snap)) (!
  (= (Set_in e (Set_union s1 s2)) (or (Set_in e s1) (Set_in e s2)))
  :pattern ((Set_in e (Set_union s1 s2)))
  :qid |$Set[Snap]_prog.in_union_in_one|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>) (e $Snap)) (!
  (=> (Set_in e s1) (Set_in e (Set_union s1 s2)))
  :pattern ((Set_in e s1) (Set_union s1 s2))
  :qid |$Set[Snap]_prog.in_left_in_union|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>) (e $Snap)) (!
  (=> (Set_in e s2) (Set_in e (Set_union s1 s2)))
  :pattern ((Set_in e s2) (Set_union s1 s2))
  :qid |$Set[Snap]_prog.in_right_in_union|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>) (e $Snap)) (!
  (= (Set_in e (Set_intersection s1 s2)) (and (Set_in e s1) (Set_in e s2)))
  :pattern ((Set_in e (Set_intersection s1 s2)))
  :pattern ((Set_intersection s1 s2) (Set_in e s1))
  :pattern ((Set_intersection s1 s2) (Set_in e s2))
  :qid |$Set[Snap]_prog.in_intersection_in_both|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>)) (!
  (= (Set_union s1 (Set_union s1 s2)) (Set_union s1 s2))
  :pattern ((Set_union s1 (Set_union s1 s2)))
  :qid |$Set[Snap]_prog.union_left_idempotency|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>)) (!
  (= (Set_union (Set_union s1 s2) s2) (Set_union s1 s2))
  :pattern ((Set_union (Set_union s1 s2) s2))
  :qid |$Set[Snap]_prog.union_right_idempotency|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>)) (!
  (= (Set_intersection s1 (Set_intersection s1 s2)) (Set_intersection s1 s2))
  :pattern ((Set_intersection s1 (Set_intersection s1 s2)))
  :qid |$Set[Snap]_prog.intersection_left_idempotency|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>)) (!
  (= (Set_intersection (Set_intersection s1 s2) s2) (Set_intersection s1 s2))
  :pattern ((Set_intersection (Set_intersection s1 s2) s2))
  :qid |$Set[Snap]_prog.intersection_right_idempotency|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>)) (!
  (=
    (+ (Set_card (Set_union s1 s2)) (Set_card (Set_intersection s1 s2)))
    (+ (Set_card s1) (Set_card s2)))
  :pattern ((Set_card (Set_union s1 s2)))
  :pattern ((Set_card (Set_intersection s1 s2)))
  :qid |$Set[Snap]_prog.cardinality_sums|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>) (e $Snap)) (!
  (= (Set_in e (Set_difference s1 s2)) (and (Set_in e s1) (not (Set_in e s2))))
  :pattern ((Set_in e (Set_difference s1 s2)))
  :qid |$Set[Snap]_prog.in_difference|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>) (e $Snap)) (!
  (=> (Set_in e s2) (not (Set_in e (Set_difference s1 s2))))
  :pattern ((Set_difference s1 s2) (Set_in e s2))
  :qid |$Set[Snap]_prog.not_in_difference|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>)) (!
  (=
    (Set_subset s1 s2)
    (forall ((e $Snap)) (!
      (=> (Set_in e s1) (Set_in e s2))
      :pattern ((Set_in e s1))
      :pattern ((Set_in e s2))
      )))
  :pattern ((Set_subset s1 s2))
  :qid |$Set[Snap]_prog.subset_definition|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>)) (!
  (=
    (Set_equal s1 s2)
    (forall ((e $Snap)) (!
      (= (Set_in e s1) (Set_in e s2))
      :pattern ((Set_in e s1))
      :pattern ((Set_in e s2))
      )))
  :pattern ((Set_equal s1 s2))
  :qid |$Set[Snap]_prog.equality_definition|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>)) (!
  (=> (Set_equal s1 s2) (= s1 s2))
  :pattern ((Set_equal s1 s2))
  :qid |$Set[Snap]_prog.native_equality|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>)) (!
  (=
    (Set_disjoint s1 s2)
    (forall ((e $Snap)) (!
      (or (not (Set_in e s1)) (not (Set_in e s2)))
      :pattern ((Set_in e s1))
      :pattern ((Set_in e s2))
      )))
  :pattern ((Set_disjoint s1 s2))
  :qid |$Set[Snap]_prog.disjointness_definition|)))
(assert (forall ((s1 Set<$Snap>) (s2 Set<$Snap>)) (!
  (and
    (=
      (+
        (+ (Set_card (Set_difference s1 s2)) (Set_card (Set_difference s2 s1)))
        (Set_card (Set_intersection s1 s2)))
      (Set_card (Set_union s1 s2)))
    (=
      (Set_card (Set_difference s1 s2))
      (- (Set_card s1) (Set_card (Set_intersection s1 s2)))))
  :pattern ((Set_card (Set_difference s1 s2)))
  :qid |$Set[Snap]_prog.cardinality_difference|)))
(assert (forall ((a IArray) (i Int)) (!
  (and (= (first<IArray> (slot<Ref> a i)) a) (= (second<Int> (slot<Ref> a i)) i))
  :pattern ((slot<Ref> a i))
  :qid |prog.all_diff|)))
(assert (forall ((a IArray)) (!
  (>= (len<Int> a) 0)
  :pattern ((len<Int> a))
  :qid |prog.len_nonneg|)))
; /field_value_functions_axioms.smt2 [val: Int]
(assert (forall ((vs $FVF<val>) (ws $FVF<val>)) (!
    (=>
      (and
        (Set_equal ($FVF.domain_val vs) ($FVF.domain_val ws))
        (forall ((x $Ref)) (!
          (=>
            (Set_in x ($FVF.domain_val vs))
            (= ($FVF.lookup_val vs x) ($FVF.lookup_val ws x)))
          :pattern (($FVF.lookup_val vs x) ($FVF.lookup_val ws x))
          :qid |qp.$FVF<val>-eq-inner|
          )))
      (= vs ws))
    :pattern (($SortWrappers.$FVF<val>To$Snap vs)
              ($SortWrappers.$FVF<val>To$Snap ws)
              )
    :qid |qp.$FVF<val>-eq-outer|
    )))
(assert (forall ((r $Ref) (pm $FPM)) (!
    ($Perm.isValidVar ($FVF.perm_val pm r))
    :pattern (($FVF.perm_val pm r)))))
(assert (forall ((r $Ref) (f Int)) (!
    (= ($FVF.loc_val f r) true)
    :pattern (($FVF.loc_val f r)))))
; End preamble
; ------------------------------------------------------------
; State saturation: after preamble
(set-option :timeout 100)
(check-sat)
; unknown
; ------------------------------------------------------------
; Begin function- and predicate-related preamble
; Declaring symbols related to program functions (from verification)
; End function- and predicate-related preamble
; ------------------------------------------------------------
; ---------- quicksort ----------
(declare-const a@0@15 IArray)
(declare-const lo@1@15 Int)
(declare-const hi@2@15 Int)
(declare-const lb@3@15 Int)
(declare-const rb@4@15 Int)
(declare-const a@5@15 IArray)
(declare-const lo@6@15 Int)
(declare-const hi@7@15 Int)
(declare-const lb@8@15 Int)
(declare-const rb@9@15 Int)
(set-option :timeout 0)
(push) ; 1
(declare-const $t@10@15 $Snap)
(assert (= $t@10@15 ($Snap.combine ($Snap.first $t@10@15) ($Snap.second $t@10@15))))
(declare-const j$0@11@15 Int)
(push) ; 2
; [eval] 0 <= j$0 && j$0 < len(a)
; [eval] 0 <= j$0
(push) ; 3
; [then-branch: 0 | 0 <= j$0@11@15 | live]
; [else-branch: 0 | !(0 <= j$0@11@15) | live]
(push) ; 4
; [then-branch: 0 | 0 <= j$0@11@15]
(assert (<= 0 j$0@11@15))
; [eval] j$0 < len(a)
; [eval] len(a)
(pop) ; 4
(push) ; 4
; [else-branch: 0 | !(0 <= j$0@11@15)]
(assert (not (<= 0 j$0@11@15)))
(pop) ; 4
(pop) ; 3
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$0@11@15)) (<= 0 j$0@11@15)))
(assert (and (< j$0@11@15 (len<Int> a@5@15)) (<= 0 j$0@11@15)))
; [eval] slot(a, j$0)
(pop) ; 2
(declare-fun inv@12@15 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$0@11@15 Int)) (!
  (=>
    (and (< j$0@11@15 (len<Int> a@5@15)) (<= 0 j$0@11@15))
    (or (not (<= 0 j$0@11@15)) (<= 0 j$0@11@15)))
  :pattern ((slot<Ref> a@5@15 j$0@11@15))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 2
(assert (not (forall ((j$01@11@15 Int) (j$02@11@15 Int)) (!
  (=>
    (and
      (and (< j$01@11@15 (len<Int> a@5@15)) (<= 0 j$01@11@15))
      (and (< j$02@11@15 (len<Int> a@5@15)) (<= 0 j$02@11@15))
      (= (slot<Ref> a@5@15 j$01@11@15) (slot<Ref> a@5@15 j$02@11@15)))
    (= j$01@11@15 j$02@11@15))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 2
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$0@11@15 Int)) (!
  (=>
    (and (< j$0@11@15 (len<Int> a@5@15)) (<= 0 j$0@11@15))
    (= (inv@12@15 (slot<Ref> a@5@15 j$0@11@15)) j$0@11@15))
  :pattern ((slot<Ref> a@5@15 j$0@11@15))
  :qid |quant-u-2|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
    (= (slot<Ref> a@5@15 (inv@12@15 r)) r))
  :pattern ((inv@12@15 r))
  :qid |val-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j$0@11@15 Int)) (!
  (=>
    (and (< j$0@11@15 (len<Int> a@5@15)) (<= 0 j$0@11@15))
    (not (= (slot<Ref> a@5@15 j$0@11@15) $Ref.null)))
  :pattern ((slot<Ref> a@5@15 j$0@11@15))
  :qid |val-permImpliesNonNull|)))
(assert (=
  ($Snap.second $t@10@15)
  ($Snap.combine
    ($Snap.first ($Snap.second $t@10@15))
    ($Snap.second ($Snap.second $t@10@15)))))
(assert (= ($Snap.first ($Snap.second $t@10@15)) $Snap.unit))
; [eval] lo >= 0
(assert (>= lo@6@15 0))
(assert (=
  ($Snap.second ($Snap.second $t@10@15))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second $t@10@15)))
    ($Snap.second ($Snap.second ($Snap.second $t@10@15))))))
(assert (= ($Snap.first ($Snap.second ($Snap.second $t@10@15))) $Snap.unit))
; [eval] hi < len(a)
; [eval] len(a)
(assert (< hi@7@15 (len<Int> a@5@15)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second $t@10@15)))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@10@15))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@10@15)))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@10@15))))
  $Snap.unit))
; [eval] hi >= -1
; [eval] -1
(assert (>= hi@7@15 (- 0 1)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@10@15))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@10@15)))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@10@15))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@10@15)))))
  $Snap.unit))
; [eval] lo <= len(a)
; [eval] len(a)
(assert (<= lo@6@15 (len<Int> a@5@15)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@10@15)))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@10@15))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@10@15)))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@10@15))))))
  $Snap.unit))
; [eval] (forall k: Int :: { slot(a, k) } lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb)
(declare-const k@13@15 Int)
(push) ; 2
; [eval] lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lo <= k && k <= hi
; [eval] lo <= k
(push) ; 3
; [then-branch: 1 | lo@6@15 <= k@13@15 | live]
; [else-branch: 1 | !(lo@6@15 <= k@13@15) | live]
(push) ; 4
; [then-branch: 1 | lo@6@15 <= k@13@15]
(assert (<= lo@6@15 k@13@15))
; [eval] k <= hi
(pop) ; 4
(push) ; 4
; [else-branch: 1 | !(lo@6@15 <= k@13@15)]
(assert (not (<= lo@6@15 k@13@15)))
(pop) ; 4
(pop) ; 3
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@6@15 k@13@15)) (<= lo@6@15 k@13@15)))
(push) ; 3
; [then-branch: 2 | k@13@15 <= hi@7@15 && lo@6@15 <= k@13@15 | live]
; [else-branch: 2 | !(k@13@15 <= hi@7@15 && lo@6@15 <= k@13@15) | live]
(push) ; 4
; [then-branch: 2 | k@13@15 <= hi@7@15 && lo@6@15 <= k@13@15]
(assert (and (<= k@13@15 hi@7@15) (<= lo@6@15 k@13@15)))
; [eval] lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lb <= slot(a, k).val
; [eval] slot(a, k)
(declare-const sm@14@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
    (=
      ($FVF.lookup_val (as sm@14@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r)))
  :pattern (($FVF.lookup_val (as sm@14@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r))
  :qid |qp.fvfValDef0|)))
(declare-const pm@15@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@15@15  $FPM) r)
    (ite
      (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@15@15  $FPM) r))
  :qid |qp.resPrmSumDef1|)))
(push) ; 5
(assert (not (< $Perm.No ($FVF.perm_val (as pm@15@15  $FPM) (slot<Ref> a@5@15 k@13@15)))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch: 3 | lb@8@15 <= Lookup(val,sm@14@15,slot[Ref](a@5@15, k@13@15)) | live]
; [else-branch: 3 | !(lb@8@15 <= Lookup(val,sm@14@15,slot[Ref](a@5@15, k@13@15))) | live]
(push) ; 6
; [then-branch: 3 | lb@8@15 <= Lookup(val,sm@14@15,slot[Ref](a@5@15, k@13@15))]
(assert (<=
  lb@8@15
  ($FVF.lookup_val (as sm@14@15  $FVF<val>) (slot<Ref> a@5@15 k@13@15))))
; [eval] slot(a, k).val <= rb
; [eval] slot(a, k)
(declare-const sm@16@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
    (=
      ($FVF.lookup_val (as sm@16@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r)))
  :pattern (($FVF.lookup_val (as sm@16@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r))
  :qid |qp.fvfValDef2|)))
(declare-const pm@17@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@17@15  $FPM) r)
    (ite
      (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@17@15  $FPM) r))
  :qid |qp.resPrmSumDef3|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@17@15  $FPM) (slot<Ref> a@5@15 k@13@15)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 3 | !(lb@8@15 <= Lookup(val,sm@14@15,slot[Ref](a@5@15, k@13@15)))]
(assert (not
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@14@15  $FVF<val>) (slot<Ref> a@5@15 k@13@15)))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
    (=
      ($FVF.lookup_val (as sm@16@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r)))
  :pattern (($FVF.lookup_val (as sm@16@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r))
  :qid |qp.fvfValDef2|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@17@15  $FPM) r)
    (ite
      (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@17@15  $FPM) r))
  :qid |qp.resPrmSumDef3|)))
; Joined path conditions
(assert (or
  (not
    (<=
      lb@8@15
      ($FVF.lookup_val (as sm@14@15  $FVF<val>) (slot<Ref> a@5@15 k@13@15))))
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@14@15  $FVF<val>) (slot<Ref> a@5@15 k@13@15)))))
(pop) ; 4
(push) ; 4
; [else-branch: 2 | !(k@13@15 <= hi@7@15 && lo@6@15 <= k@13@15)]
(assert (not (and (<= k@13@15 hi@7@15) (<= lo@6@15 k@13@15))))
(pop) ; 4
(pop) ; 3
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
    (=
      ($FVF.lookup_val (as sm@14@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r)))
  :pattern (($FVF.lookup_val (as sm@14@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r))
  :qid |qp.fvfValDef0|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@15@15  $FPM) r)
    (ite
      (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@15@15  $FPM) r))
  :qid |qp.resPrmSumDef1|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
    (=
      ($FVF.lookup_val (as sm@16@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r)))
  :pattern (($FVF.lookup_val (as sm@16@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r))
  :qid |qp.fvfValDef2|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@17@15  $FPM) r)
    (ite
      (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@17@15  $FPM) r))
  :qid |qp.resPrmSumDef3|)))
(assert (=>
  (and (<= k@13@15 hi@7@15) (<= lo@6@15 k@13@15))
  (and
    (<= k@13@15 hi@7@15)
    (<= lo@6@15 k@13@15)
    (or
      (not
        (<=
          lb@8@15
          ($FVF.lookup_val (as sm@14@15  $FVF<val>) (slot<Ref> a@5@15 k@13@15))))
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@14@15  $FVF<val>) (slot<Ref> a@5@15 k@13@15)))))))
; Joined path conditions
(assert (or
  (not (and (<= k@13@15 hi@7@15) (<= lo@6@15 k@13@15)))
  (and (<= k@13@15 hi@7@15) (<= lo@6@15 k@13@15))))
(pop) ; 2
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
    (=
      ($FVF.lookup_val (as sm@14@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r)))
  :pattern (($FVF.lookup_val (as sm@14@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r))
  :qid |qp.fvfValDef0|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@15@15  $FPM) r)
    (ite
      (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@15@15  $FPM) r))
  :qid |qp.resPrmSumDef1|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
    (=
      ($FVF.lookup_val (as sm@16@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r)))
  :pattern (($FVF.lookup_val (as sm@16@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r))
  :qid |qp.fvfValDef2|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@17@15  $FPM) r)
    (ite
      (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@17@15  $FPM) r))
  :qid |qp.resPrmSumDef3|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@13@15 Int)) (!
  (and
    (or (not (<= lo@6@15 k@13@15)) (<= lo@6@15 k@13@15))
    (=>
      (and (<= k@13@15 hi@7@15) (<= lo@6@15 k@13@15))
      (and
        (<= k@13@15 hi@7@15)
        (<= lo@6@15 k@13@15)
        (or
          (not
            (<=
              lb@8@15
              ($FVF.lookup_val (as sm@14@15  $FVF<val>) (slot<Ref> a@5@15 k@13@15))))
          (<=
            lb@8@15
            ($FVF.lookup_val (as sm@14@15  $FVF<val>) (slot<Ref> a@5@15 k@13@15))))))
    (or
      (not (and (<= k@13@15 hi@7@15) (<= lo@6@15 k@13@15)))
      (and (<= k@13@15 hi@7@15) (<= lo@6@15 k@13@15))))
  :pattern ((slot<Ref> a@5@15 k@13@15))
  :qid |prog.l81-aux|)))
(assert (forall ((k@13@15 Int)) (!
  (=>
    (and (<= k@13@15 hi@7@15) (<= lo@6@15 k@13@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@16@15  $FVF<val>) (slot<Ref> a@5@15 k@13@15))
        rb@9@15)
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@14@15  $FVF<val>) (slot<Ref> a@5@15 k@13@15)))))
  :pattern ((slot<Ref> a@5@15 k@13@15))
  :qid |prog.l81|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@10@15))))))
  $Snap.unit))
; [eval] lb <= rb
(assert (<= lb@8@15 rb@9@15))
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
(set-option :timeout 0)
(push) ; 2
(declare-const $t@18@15 $Snap)
(assert (= $t@18@15 ($Snap.combine ($Snap.first $t@18@15) ($Snap.second $t@18@15))))
(declare-const j$1@19@15 Int)
(push) ; 3
; [eval] 0 <= j$1 && j$1 < len(a)
; [eval] 0 <= j$1
(push) ; 4
; [then-branch: 4 | 0 <= j$1@19@15 | live]
; [else-branch: 4 | !(0 <= j$1@19@15) | live]
(push) ; 5
; [then-branch: 4 | 0 <= j$1@19@15]
(assert (<= 0 j$1@19@15))
; [eval] j$1 < len(a)
; [eval] len(a)
(pop) ; 5
(push) ; 5
; [else-branch: 4 | !(0 <= j$1@19@15)]
(assert (not (<= 0 j$1@19@15)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$1@19@15)) (<= 0 j$1@19@15)))
(assert (and (< j$1@19@15 (len<Int> a@5@15)) (<= 0 j$1@19@15)))
; [eval] slot(a, j$1)
(pop) ; 3
(declare-fun inv@20@15 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$1@19@15 Int)) (!
  (=>
    (and (< j$1@19@15 (len<Int> a@5@15)) (<= 0 j$1@19@15))
    (or (not (<= 0 j$1@19@15)) (<= 0 j$1@19@15)))
  :pattern ((slot<Ref> a@5@15 j$1@19@15))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 3
(assert (not (forall ((j$11@19@15 Int) (j$12@19@15 Int)) (!
  (=>
    (and
      (and (< j$11@19@15 (len<Int> a@5@15)) (<= 0 j$11@19@15))
      (and (< j$12@19@15 (len<Int> a@5@15)) (<= 0 j$12@19@15))
      (= (slot<Ref> a@5@15 j$11@19@15) (slot<Ref> a@5@15 j$12@19@15)))
    (= j$11@19@15 j$12@19@15))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$1@19@15 Int)) (!
  (=>
    (and (< j$1@19@15 (len<Int> a@5@15)) (<= 0 j$1@19@15))
    (= (inv@20@15 (slot<Ref> a@5@15 j$1@19@15)) j$1@19@15))
  :pattern ((slot<Ref> a@5@15 j$1@19@15))
  :qid |quant-u-6|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (= (slot<Ref> a@5@15 (inv@20@15 r)) r))
  :pattern ((inv@20@15 r))
  :qid |val-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j$1@19@15 Int)) (!
  (=>
    (and (< j$1@19@15 (len<Int> a@5@15)) (<= 0 j$1@19@15))
    (not (= (slot<Ref> a@5@15 j$1@19@15) $Ref.null)))
  :pattern ((slot<Ref> a@5@15 j$1@19@15))
  :qid |val-permImpliesNonNull|)))
(assert (=
  ($Snap.second $t@18@15)
  ($Snap.combine
    ($Snap.first ($Snap.second $t@18@15))
    ($Snap.second ($Snap.second $t@18@15)))))
(assert (= ($Snap.first ($Snap.second $t@18@15)) $Snap.unit))
; [eval] (forall k$0: Int :: { slot(a, k$0) } lo <= k$0 && k$0 <= hi ==> lb <= slot(a, k$0).val && slot(a, k$0).val <= rb)
(declare-const k$0@21@15 Int)
(push) ; 3
; [eval] lo <= k$0 && k$0 <= hi ==> lb <= slot(a, k$0).val && slot(a, k$0).val <= rb
; [eval] lo <= k$0 && k$0 <= hi
; [eval] lo <= k$0
(push) ; 4
; [then-branch: 5 | lo@6@15 <= k$0@21@15 | live]
; [else-branch: 5 | !(lo@6@15 <= k$0@21@15) | live]
(push) ; 5
; [then-branch: 5 | lo@6@15 <= k$0@21@15]
(assert (<= lo@6@15 k$0@21@15))
; [eval] k$0 <= hi
(pop) ; 5
(push) ; 5
; [else-branch: 5 | !(lo@6@15 <= k$0@21@15)]
(assert (not (<= lo@6@15 k$0@21@15)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@6@15 k$0@21@15)) (<= lo@6@15 k$0@21@15)))
(push) ; 4
; [then-branch: 6 | k$0@21@15 <= hi@7@15 && lo@6@15 <= k$0@21@15 | live]
; [else-branch: 6 | !(k$0@21@15 <= hi@7@15 && lo@6@15 <= k$0@21@15) | live]
(push) ; 5
; [then-branch: 6 | k$0@21@15 <= hi@7@15 && lo@6@15 <= k$0@21@15]
(assert (and (<= k$0@21@15 hi@7@15) (<= lo@6@15 k$0@21@15)))
; [eval] lb <= slot(a, k$0).val && slot(a, k$0).val <= rb
; [eval] lb <= slot(a, k$0).val
; [eval] slot(a, k$0)
(declare-const sm@22@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@22@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@22@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef4|)))
(declare-const pm@23@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@23@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@23@15  $FPM) r))
  :qid |qp.resPrmSumDef5|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@23@15  $FPM) (slot<Ref> a@5@15 k$0@21@15)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch: 7 | lb@8@15 <= Lookup(val,sm@22@15,slot[Ref](a@5@15, k$0@21@15)) | live]
; [else-branch: 7 | !(lb@8@15 <= Lookup(val,sm@22@15,slot[Ref](a@5@15, k$0@21@15))) | live]
(push) ; 7
; [then-branch: 7 | lb@8@15 <= Lookup(val,sm@22@15,slot[Ref](a@5@15, k$0@21@15))]
(assert (<=
  lb@8@15
  ($FVF.lookup_val (as sm@22@15  $FVF<val>) (slot<Ref> a@5@15 k$0@21@15))))
; [eval] slot(a, k$0).val <= rb
; [eval] slot(a, k$0)
(declare-const sm@24@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@24@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@24@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef6|)))
(declare-const pm@25@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@25@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@25@15  $FPM) r))
  :qid |qp.resPrmSumDef7|)))
(push) ; 8
(assert (not (< $Perm.No ($FVF.perm_val (as pm@25@15  $FPM) (slot<Ref> a@5@15 k$0@21@15)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(pop) ; 7
(push) ; 7
; [else-branch: 7 | !(lb@8@15 <= Lookup(val,sm@22@15,slot[Ref](a@5@15, k$0@21@15)))]
(assert (not
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@22@15  $FVF<val>) (slot<Ref> a@5@15 k$0@21@15)))))
(pop) ; 7
(pop) ; 6
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@24@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@24@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef6|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@25@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@25@15  $FPM) r))
  :qid |qp.resPrmSumDef7|)))
; Joined path conditions
(assert (or
  (not
    (<=
      lb@8@15
      ($FVF.lookup_val (as sm@22@15  $FVF<val>) (slot<Ref> a@5@15 k$0@21@15))))
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@22@15  $FVF<val>) (slot<Ref> a@5@15 k$0@21@15)))))
(pop) ; 5
(push) ; 5
; [else-branch: 6 | !(k$0@21@15 <= hi@7@15 && lo@6@15 <= k$0@21@15)]
(assert (not (and (<= k$0@21@15 hi@7@15) (<= lo@6@15 k$0@21@15))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@22@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@22@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef4|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@23@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@23@15  $FPM) r))
  :qid |qp.resPrmSumDef5|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@24@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@24@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef6|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@25@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@25@15  $FPM) r))
  :qid |qp.resPrmSumDef7|)))
(assert (=>
  (and (<= k$0@21@15 hi@7@15) (<= lo@6@15 k$0@21@15))
  (and
    (<= k$0@21@15 hi@7@15)
    (<= lo@6@15 k$0@21@15)
    (or
      (not
        (<=
          lb@8@15
          ($FVF.lookup_val (as sm@22@15  $FVF<val>) (slot<Ref> a@5@15 k$0@21@15))))
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@22@15  $FVF<val>) (slot<Ref> a@5@15 k$0@21@15)))))))
; Joined path conditions
(assert (or
  (not (and (<= k$0@21@15 hi@7@15) (<= lo@6@15 k$0@21@15)))
  (and (<= k$0@21@15 hi@7@15) (<= lo@6@15 k$0@21@15))))
(pop) ; 3
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@22@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@22@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef4|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@23@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@23@15  $FPM) r))
  :qid |qp.resPrmSumDef5|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@24@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@24@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef6|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@25@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@25@15  $FPM) r))
  :qid |qp.resPrmSumDef7|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$0@21@15 Int)) (!
  (and
    (or (not (<= lo@6@15 k$0@21@15)) (<= lo@6@15 k$0@21@15))
    (=>
      (and (<= k$0@21@15 hi@7@15) (<= lo@6@15 k$0@21@15))
      (and
        (<= k$0@21@15 hi@7@15)
        (<= lo@6@15 k$0@21@15)
        (or
          (not
            (<=
              lb@8@15
              ($FVF.lookup_val (as sm@22@15  $FVF<val>) (slot<Ref> a@5@15 k$0@21@15))))
          (<=
            lb@8@15
            ($FVF.lookup_val (as sm@22@15  $FVF<val>) (slot<Ref> a@5@15 k$0@21@15))))))
    (or
      (not (and (<= k$0@21@15 hi@7@15) (<= lo@6@15 k$0@21@15)))
      (and (<= k$0@21@15 hi@7@15) (<= lo@6@15 k$0@21@15))))
  :pattern ((slot<Ref> a@5@15 k$0@21@15))
  :qid |prog.l87-aux|)))
(assert (forall ((k$0@21@15 Int)) (!
  (=>
    (and (<= k$0@21@15 hi@7@15) (<= lo@6@15 k$0@21@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@24@15  $FVF<val>) (slot<Ref> a@5@15 k$0@21@15))
        rb@9@15)
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@22@15  $FVF<val>) (slot<Ref> a@5@15 k$0@21@15)))))
  :pattern ((slot<Ref> a@5@15 k$0@21@15))
  :qid |prog.l87|)))
(assert (= ($Snap.second ($Snap.second $t@18@15)) $Snap.unit))
; [eval] (forall i: Int, j: Int :: { slot(a, i), slot(a, j) } lo <= i && (i <= j && j <= hi) ==> slot(a, i).val <= slot(a, j).val)
(declare-const i@26@15 Int)
(declare-const j@27@15 Int)
(push) ; 3
; [eval] lo <= i && (i <= j && j <= hi) ==> slot(a, i).val <= slot(a, j).val
; [eval] lo <= i && (i <= j && j <= hi)
; [eval] lo <= i
(push) ; 4
; [then-branch: 8 | lo@6@15 <= i@26@15 | live]
; [else-branch: 8 | !(lo@6@15 <= i@26@15) | live]
(push) ; 5
; [then-branch: 8 | lo@6@15 <= i@26@15]
(assert (<= lo@6@15 i@26@15))
; [eval] i <= j
(push) ; 6
; [then-branch: 9 | i@26@15 <= j@27@15 | live]
; [else-branch: 9 | !(i@26@15 <= j@27@15) | live]
(push) ; 7
; [then-branch: 9 | i@26@15 <= j@27@15]
(assert (<= i@26@15 j@27@15))
; [eval] j <= hi
(pop) ; 7
(push) ; 7
; [else-branch: 9 | !(i@26@15 <= j@27@15)]
(assert (not (<= i@26@15 j@27@15)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (or (not (<= i@26@15 j@27@15)) (<= i@26@15 j@27@15)))
(pop) ; 5
(push) ; 5
; [else-branch: 8 | !(lo@6@15 <= i@26@15)]
(assert (not (<= lo@6@15 i@26@15)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (=>
  (<= lo@6@15 i@26@15)
  (and (<= lo@6@15 i@26@15) (or (not (<= i@26@15 j@27@15)) (<= i@26@15 j@27@15)))))
; Joined path conditions
(assert (or (not (<= lo@6@15 i@26@15)) (<= lo@6@15 i@26@15)))
(push) ; 4
; [then-branch: 10 | j@27@15 <= hi@7@15 && i@26@15 <= j@27@15 && lo@6@15 <= i@26@15 | live]
; [else-branch: 10 | !(j@27@15 <= hi@7@15 && i@26@15 <= j@27@15 && lo@6@15 <= i@26@15) | live]
(push) ; 5
; [then-branch: 10 | j@27@15 <= hi@7@15 && i@26@15 <= j@27@15 && lo@6@15 <= i@26@15]
(assert (and (and (<= j@27@15 hi@7@15) (<= i@26@15 j@27@15)) (<= lo@6@15 i@26@15)))
; [eval] slot(a, i).val <= slot(a, j).val
; [eval] slot(a, i)
(declare-const sm@28@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@28@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@28@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef8|)))
(declare-const pm@29@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@29@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@29@15  $FPM) r))
  :qid |qp.resPrmSumDef9|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@29@15  $FPM) (slot<Ref> a@5@15 i@26@15)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] slot(a, j)
(declare-const sm@30@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@30@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@30@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef10|)))
(declare-const pm@31@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@31@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@31@15  $FPM) r))
  :qid |qp.resPrmSumDef11|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@31@15  $FPM) (slot<Ref> a@5@15 j@27@15)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(pop) ; 5
(push) ; 5
; [else-branch: 10 | !(j@27@15 <= hi@7@15 && i@26@15 <= j@27@15 && lo@6@15 <= i@26@15)]
(assert (not (and (and (<= j@27@15 hi@7@15) (<= i@26@15 j@27@15)) (<= lo@6@15 i@26@15))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@28@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@28@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef8|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@29@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@29@15  $FPM) r))
  :qid |qp.resPrmSumDef9|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@30@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@30@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef10|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@31@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@31@15  $FPM) r))
  :qid |qp.resPrmSumDef11|)))
(assert (=>
  (and (and (<= j@27@15 hi@7@15) (<= i@26@15 j@27@15)) (<= lo@6@15 i@26@15))
  (and (<= j@27@15 hi@7@15) (<= i@26@15 j@27@15) (<= lo@6@15 i@26@15))))
; Joined path conditions
(assert (or
  (not
    (and (and (<= j@27@15 hi@7@15) (<= i@26@15 j@27@15)) (<= lo@6@15 i@26@15)))
  (and (and (<= j@27@15 hi@7@15) (<= i@26@15 j@27@15)) (<= lo@6@15 i@26@15))))
(pop) ; 3
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@28@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@28@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef8|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@29@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@29@15  $FPM) r))
  :qid |qp.resPrmSumDef9|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
    (=
      ($FVF.lookup_val (as sm@30@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r)))
  :pattern (($FVF.lookup_val (as sm@30@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@18@15)) r))
  :qid |qp.fvfValDef10|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@31@15  $FPM) r)
    (ite
      (and (< (inv@20@15 r) (len<Int> a@5@15)) (<= 0 (inv@20@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@31@15  $FPM) r))
  :qid |qp.resPrmSumDef11|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((i@26@15 Int) (j@27@15 Int)) (!
  (and
    (=>
      (<= lo@6@15 i@26@15)
      (and
        (<= lo@6@15 i@26@15)
        (or (not (<= i@26@15 j@27@15)) (<= i@26@15 j@27@15))))
    (or (not (<= lo@6@15 i@26@15)) (<= lo@6@15 i@26@15))
    (=>
      (and (and (<= j@27@15 hi@7@15) (<= i@26@15 j@27@15)) (<= lo@6@15 i@26@15))
      (and (<= j@27@15 hi@7@15) (<= i@26@15 j@27@15) (<= lo@6@15 i@26@15)))
    (or
      (not
        (and
          (and (<= j@27@15 hi@7@15) (<= i@26@15 j@27@15))
          (<= lo@6@15 i@26@15)))
      (and (and (<= j@27@15 hi@7@15) (<= i@26@15 j@27@15)) (<= lo@6@15 i@26@15))))
  :pattern ((slot<Ref> a@5@15 i@26@15) (slot<Ref> a@5@15 j@27@15))
  :qid |prog.l88-aux|)))
(assert (forall ((i@26@15 Int) (j@27@15 Int)) (!
  (=>
    (and (and (<= j@27@15 hi@7@15) (<= i@26@15 j@27@15)) (<= lo@6@15 i@26@15))
    (<=
      ($FVF.lookup_val (as sm@28@15  $FVF<val>) (slot<Ref> a@5@15 i@26@15))
      ($FVF.lookup_val (as sm@30@15  $FVF<val>) (slot<Ref> a@5@15 j@27@15))))
  :pattern ((slot<Ref> a@5@15 i@26@15) (slot<Ref> a@5@15 j@27@15))
  :qid |prog.l88|)))
(pop) ; 2
(push) ; 2
; [eval] lo < hi
(push) ; 3
(set-option :timeout 10)
(assert (not (not (< lo@6@15 hi@7@15))))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 3
(set-option :timeout 10)
(assert (not (< lo@6@15 hi@7@15)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
; [then-branch: 11 | lo@6@15 < hi@7@15 | live]
; [else-branch: 11 | !(lo@6@15 < hi@7@15) | live]
(set-option :timeout 0)
(push) ; 3
; [then-branch: 11 | lo@6@15 < hi@7@15]
(assert (< lo@6@15 hi@7@15))
; [exec]
; var p: Int
(declare-const p@32@15 Int)
; [exec]
; var pivot: Int
(declare-const pivot@33@15 Int)
; [exec]
; p := partition(a, lo, hi, lb, rb)
(declare-const j$0@34@15 Int)
(push) ; 4
; [eval] 0 <= j$0 && j$0 < len(a)
; [eval] 0 <= j$0
(push) ; 5
; [then-branch: 12 | 0 <= j$0@34@15 | live]
; [else-branch: 12 | !(0 <= j$0@34@15) | live]
(push) ; 6
; [then-branch: 12 | 0 <= j$0@34@15]
(assert (<= 0 j$0@34@15))
; [eval] j$0 < len(a)
; [eval] len(a)
(pop) ; 6
(push) ; 6
; [else-branch: 12 | !(0 <= j$0@34@15)]
(assert (not (<= 0 j$0@34@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$0@34@15)) (<= 0 j$0@34@15)))
(assert (and (< j$0@34@15 (len<Int> a@5@15)) (<= 0 j$0@34@15)))
; [eval] slot(a, j$0)
(pop) ; 4
(declare-fun inv@35@15 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$0@34@15 Int)) (!
  (=>
    (and (< j$0@34@15 (len<Int> a@5@15)) (<= 0 j$0@34@15))
    (or (not (<= 0 j$0@34@15)) (<= 0 j$0@34@15)))
  :pattern ((slot<Ref> a@5@15 j$0@34@15))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 4
(assert (not (forall ((j$01@34@15 Int) (j$02@34@15 Int)) (!
  (=>
    (and
      (and (< j$01@34@15 (len<Int> a@5@15)) (<= 0 j$01@34@15))
      (and (< j$02@34@15 (len<Int> a@5@15)) (<= 0 j$02@34@15))
      (= (slot<Ref> a@5@15 j$01@34@15) (slot<Ref> a@5@15 j$02@34@15)))
    (= j$01@34@15 j$02@34@15))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$0@34@15 Int)) (!
  (=>
    (and (< j$0@34@15 (len<Int> a@5@15)) (<= 0 j$0@34@15))
    (= (inv@35@15 (slot<Ref> a@5@15 j$0@34@15)) j$0@34@15))
  :pattern ((slot<Ref> a@5@15 j$0@34@15))
  :qid |val-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@35@15 r) (len<Int> a@5@15)) (<= 0 (inv@35@15 r)))
    (= (slot<Ref> a@5@15 (inv@35@15 r)) r))
  :pattern ((inv@35@15 r))
  :qid |val-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@36@15 ((r $Ref)) $Perm
  (ite
    (and (< (inv@35@15 r) (len<Int> a@5@15)) (<= 0 (inv@35@15 r)))
    ($Perm.min
      (ite
        (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Chunk depleted?
(set-option :timeout 0)
(push) ; 4
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (ite
        (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
        $Perm.Write
        $Perm.No)
      (pTaken@36@15 r))
    $Perm.No)
  
  :qid |quant-u-10|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 4
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (and (< (inv@35@15 r) (len<Int> a@5@15)) (<= 0 (inv@35@15 r)))
    (= (- $Perm.Write (pTaken@36@15 r)) $Perm.No))
  
  :qid |quant-u-11|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@37@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@12@15 r) (len<Int> a@5@15)) (<= 0 (inv@12@15 r)))
    (=
      ($FVF.lookup_val (as sm@37@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r)))
  :pattern (($FVF.lookup_val (as sm@37@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@10@15)) r))
  :qid |qp.fvfValDef12|)))
; [eval] hi >= 0
(set-option :timeout 0)
(push) ; 4
(assert (not (>= hi@7@15 0)))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (>= hi@7@15 0))
; [eval] hi < len(a)
; [eval] len(a)
; [eval] lo >= 0
; [eval] lo <= hi
(push) ; 4
(assert (not (<= lo@6@15 hi@7@15)))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (<= lo@6@15 hi@7@15))
; [eval] (forall k$0: Int :: { slot(a, k$0) } lo <= k$0 && k$0 <= hi ==> lb <= slot(a, k$0).val && slot(a, k$0).val <= rb)
(declare-const k$0@38@15 Int)
(push) ; 4
; [eval] lo <= k$0 && k$0 <= hi ==> lb <= slot(a, k$0).val && slot(a, k$0).val <= rb
; [eval] lo <= k$0 && k$0 <= hi
; [eval] lo <= k$0
(push) ; 5
; [then-branch: 13 | lo@6@15 <= k$0@38@15 | live]
; [else-branch: 13 | !(lo@6@15 <= k$0@38@15) | live]
(push) ; 6
; [then-branch: 13 | lo@6@15 <= k$0@38@15]
(assert (<= lo@6@15 k$0@38@15))
; [eval] k$0 <= hi
(pop) ; 6
(push) ; 6
; [else-branch: 13 | !(lo@6@15 <= k$0@38@15)]
(assert (not (<= lo@6@15 k$0@38@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@6@15 k$0@38@15)) (<= lo@6@15 k$0@38@15)))
(push) ; 5
; [then-branch: 14 | k$0@38@15 <= hi@7@15 && lo@6@15 <= k$0@38@15 | live]
; [else-branch: 14 | !(k$0@38@15 <= hi@7@15 && lo@6@15 <= k$0@38@15) | live]
(push) ; 6
; [then-branch: 14 | k$0@38@15 <= hi@7@15 && lo@6@15 <= k$0@38@15]
(assert (and (<= k$0@38@15 hi@7@15) (<= lo@6@15 k$0@38@15)))
; [eval] lb <= slot(a, k$0).val && slot(a, k$0).val <= rb
; [eval] lb <= slot(a, k$0).val
; [eval] slot(a, k$0)
(push) ; 7
(assert (not (and
  (< (inv@12@15 (slot<Ref> a@5@15 k$0@38@15)) (len<Int> a@5@15))
  (<= 0 (inv@12@15 (slot<Ref> a@5@15 k$0@38@15))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch: 15 | lb@8@15 <= Lookup(val,sm@37@15,slot[Ref](a@5@15, k$0@38@15)) | live]
; [else-branch: 15 | !(lb@8@15 <= Lookup(val,sm@37@15,slot[Ref](a@5@15, k$0@38@15))) | live]
(push) ; 8
; [then-branch: 15 | lb@8@15 <= Lookup(val,sm@37@15,slot[Ref](a@5@15, k$0@38@15))]
(assert (<=
  lb@8@15
  ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15))))
; [eval] slot(a, k$0).val <= rb
; [eval] slot(a, k$0)
(push) ; 9
(assert (not (and
  (< (inv@12@15 (slot<Ref> a@5@15 k$0@38@15)) (len<Int> a@5@15))
  (<= 0 (inv@12@15 (slot<Ref> a@5@15 k$0@38@15))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 15 | !(lb@8@15 <= Lookup(val,sm@37@15,slot[Ref](a@5@15, k$0@38@15)))]
(assert (not
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15)))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (<=
      lb@8@15
      ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15))))
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15)))))
(pop) ; 6
(push) ; 6
; [else-branch: 14 | !(k$0@38@15 <= hi@7@15 && lo@6@15 <= k$0@38@15)]
(assert (not (and (<= k$0@38@15 hi@7@15) (<= lo@6@15 k$0@38@15))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (=>
  (and (<= k$0@38@15 hi@7@15) (<= lo@6@15 k$0@38@15))
  (and
    (<= k$0@38@15 hi@7@15)
    (<= lo@6@15 k$0@38@15)
    (or
      (not
        (<=
          lb@8@15
          ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15))))
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15)))))))
; Joined path conditions
(assert (or
  (not (and (<= k$0@38@15 hi@7@15) (<= lo@6@15 k$0@38@15)))
  (and (<= k$0@38@15 hi@7@15) (<= lo@6@15 k$0@38@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$0@38@15 Int)) (!
  (and
    (or (not (<= lo@6@15 k$0@38@15)) (<= lo@6@15 k$0@38@15))
    (=>
      (and (<= k$0@38@15 hi@7@15) (<= lo@6@15 k$0@38@15))
      (and
        (<= k$0@38@15 hi@7@15)
        (<= lo@6@15 k$0@38@15)
        (or
          (not
            (<=
              lb@8@15
              ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15))))
          (<=
            lb@8@15
            ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15))))))
    (or
      (not (and (<= k$0@38@15 hi@7@15) (<= lo@6@15 k$0@38@15)))
      (and (<= k$0@38@15 hi@7@15) (<= lo@6@15 k$0@38@15))))
  :pattern ((slot<Ref> a@5@15 k$0@38@15))
  :qid |prog.l36-aux|)))
(push) ; 4
(assert (not (forall ((k$0@38@15 Int)) (!
  (=>
    (and (<= k$0@38@15 hi@7@15) (<= lo@6@15 k$0@38@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15))
        rb@9@15)
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15)))))
  :pattern ((slot<Ref> a@5@15 k$0@38@15))
  :qid |prog.l36|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k$0@38@15 Int)) (!
  (=>
    (and (<= k$0@38@15 hi@7@15) (<= lo@6@15 k$0@38@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15))
        rb@9@15)
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$0@38@15)))))
  :pattern ((slot<Ref> a@5@15 k$0@38@15))
  :qid |prog.l36|)))
(declare-const i@39@15 Int)
(declare-const $t@40@15 $Snap)
(assert (= $t@40@15 ($Snap.combine ($Snap.first $t@40@15) ($Snap.second $t@40@15))))
(declare-const j$1@41@15 Int)
(push) ; 4
; [eval] 0 <= j$1 && j$1 < len(a)
; [eval] 0 <= j$1
(push) ; 5
; [then-branch: 16 | 0 <= j$1@41@15 | live]
; [else-branch: 16 | !(0 <= j$1@41@15) | live]
(push) ; 6
; [then-branch: 16 | 0 <= j$1@41@15]
(assert (<= 0 j$1@41@15))
; [eval] j$1 < len(a)
; [eval] len(a)
(pop) ; 6
(push) ; 6
; [else-branch: 16 | !(0 <= j$1@41@15)]
(assert (not (<= 0 j$1@41@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$1@41@15)) (<= 0 j$1@41@15)))
(assert (and (< j$1@41@15 (len<Int> a@5@15)) (<= 0 j$1@41@15)))
; [eval] slot(a, j$1)
(pop) ; 4
(declare-fun inv@42@15 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$1@41@15 Int)) (!
  (=>
    (and (< j$1@41@15 (len<Int> a@5@15)) (<= 0 j$1@41@15))
    (or (not (<= 0 j$1@41@15)) (<= 0 j$1@41@15)))
  :pattern ((slot<Ref> a@5@15 j$1@41@15))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 4
(assert (not (forall ((j$11@41@15 Int) (j$12@41@15 Int)) (!
  (=>
    (and
      (and (< j$11@41@15 (len<Int> a@5@15)) (<= 0 j$11@41@15))
      (and (< j$12@41@15 (len<Int> a@5@15)) (<= 0 j$12@41@15))
      (= (slot<Ref> a@5@15 j$11@41@15) (slot<Ref> a@5@15 j$12@41@15)))
    (= j$11@41@15 j$12@41@15))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$1@41@15 Int)) (!
  (=>
    (and (< j$1@41@15 (len<Int> a@5@15)) (<= 0 j$1@41@15))
    (= (inv@42@15 (slot<Ref> a@5@15 j$1@41@15)) j$1@41@15))
  :pattern ((slot<Ref> a@5@15 j$1@41@15))
  :qid |quant-u-13|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (= (slot<Ref> a@5@15 (inv@42@15 r)) r))
  :pattern ((inv@42@15 r))
  :qid |val-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j$1@41@15 Int)) (!
  (=>
    (and (< j$1@41@15 (len<Int> a@5@15)) (<= 0 j$1@41@15))
    (not (= (slot<Ref> a@5@15 j$1@41@15) $Ref.null)))
  :pattern ((slot<Ref> a@5@15 j$1@41@15))
  :qid |val-permImpliesNonNull|)))
(assert (=
  ($Snap.second $t@40@15)
  ($Snap.combine
    ($Snap.first ($Snap.second $t@40@15))
    ($Snap.second ($Snap.second $t@40@15)))))
(assert (= ($Snap.first ($Snap.second $t@40@15)) $Snap.unit))
; [eval] i >= lo
(assert (>= i@39@15 lo@6@15))
(assert (=
  ($Snap.second ($Snap.second $t@40@15))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second $t@40@15)))
    ($Snap.second ($Snap.second ($Snap.second $t@40@15))))))
(assert (= ($Snap.first ($Snap.second ($Snap.second $t@40@15))) $Snap.unit))
; [eval] i <= hi
(assert (<= i@39@15 hi@7@15))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second $t@40@15)))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@40@15))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15)))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@40@15))))
  $Snap.unit))
; [eval] (forall k: Int :: { slot(a, k) } k >= lo && k <= i ==> slot(a, k).val <= slot(a, i).val)
(declare-const k@43@15 Int)
(push) ; 4
; [eval] k >= lo && k <= i ==> slot(a, k).val <= slot(a, i).val
; [eval] k >= lo && k <= i
; [eval] k >= lo
(push) ; 5
; [then-branch: 17 | k@43@15 >= lo@6@15 | live]
; [else-branch: 17 | !(k@43@15 >= lo@6@15) | live]
(push) ; 6
; [then-branch: 17 | k@43@15 >= lo@6@15]
(assert (>= k@43@15 lo@6@15))
; [eval] k <= i
(pop) ; 6
(push) ; 6
; [else-branch: 17 | !(k@43@15 >= lo@6@15)]
(assert (not (>= k@43@15 lo@6@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@43@15 lo@6@15)) (>= k@43@15 lo@6@15)))
(push) ; 5
; [then-branch: 18 | k@43@15 <= i@39@15 && k@43@15 >= lo@6@15 | live]
; [else-branch: 18 | !(k@43@15 <= i@39@15 && k@43@15 >= lo@6@15) | live]
(push) ; 6
; [then-branch: 18 | k@43@15 <= i@39@15 && k@43@15 >= lo@6@15]
(assert (and (<= k@43@15 i@39@15) (>= k@43@15 lo@6@15)))
; [eval] slot(a, k).val <= slot(a, i).val
; [eval] slot(a, k)
(declare-const sm@44@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@44@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@44@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef13|)))
(declare-const pm@45@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@45@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@45@15  $FPM) r))
  :qid |qp.resPrmSumDef14|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@45@15  $FPM) (slot<Ref> a@5@15 k@43@15)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [eval] slot(a, i)
(declare-const sm@46@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@46@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@46@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef15|)))
(declare-const pm@47@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@47@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@47@15  $FPM) r))
  :qid |qp.resPrmSumDef16|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@47@15  $FPM) (slot<Ref> a@5@15 i@39@15)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 18 | !(k@43@15 <= i@39@15 && k@43@15 >= lo@6@15)]
(assert (not (and (<= k@43@15 i@39@15) (>= k@43@15 lo@6@15))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@44@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@44@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef13|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@45@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@45@15  $FPM) r))
  :qid |qp.resPrmSumDef14|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@46@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@46@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef15|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@47@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@47@15  $FPM) r))
  :qid |qp.resPrmSumDef16|)))
; Joined path conditions
(assert (or
  (not (and (<= k@43@15 i@39@15) (>= k@43@15 lo@6@15)))
  (and (<= k@43@15 i@39@15) (>= k@43@15 lo@6@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@44@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@44@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef13|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@45@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@45@15  $FPM) r))
  :qid |qp.resPrmSumDef14|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@46@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@46@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef15|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@47@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@47@15  $FPM) r))
  :qid |qp.resPrmSumDef16|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@43@15 Int)) (!
  (and
    (or (not (>= k@43@15 lo@6@15)) (>= k@43@15 lo@6@15))
    (or
      (not (and (<= k@43@15 i@39@15) (>= k@43@15 lo@6@15)))
      (and (<= k@43@15 i@39@15) (>= k@43@15 lo@6@15))))
  :pattern ((slot<Ref> a@5@15 k@43@15))
  :qid |prog.l39-aux|)))
(assert (forall ((k@43@15 Int)) (!
  (=>
    (and (<= k@43@15 i@39@15) (>= k@43@15 lo@6@15))
    (<=
      ($FVF.lookup_val (as sm@44@15  $FVF<val>) (slot<Ref> a@5@15 k@43@15))
      ($FVF.lookup_val (as sm@46@15  $FVF<val>) (slot<Ref> a@5@15 i@39@15))))
  :pattern ((slot<Ref> a@5@15 k@43@15))
  :qid |prog.l39|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15)))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15)))))
  $Snap.unit))
; [eval] (forall k: Int :: { slot(a, k) } k >= i + 1 && k <= hi ==> slot(a, k).val > slot(a, i).val)
(declare-const k@48@15 Int)
(push) ; 4
; [eval] k >= i + 1 && k <= hi ==> slot(a, k).val > slot(a, i).val
; [eval] k >= i + 1 && k <= hi
; [eval] k >= i + 1
; [eval] i + 1
(push) ; 5
; [then-branch: 19 | k@48@15 >= i@39@15 + 1 | live]
; [else-branch: 19 | !(k@48@15 >= i@39@15 + 1) | live]
(push) ; 6
; [then-branch: 19 | k@48@15 >= i@39@15 + 1]
(assert (>= k@48@15 (+ i@39@15 1)))
; [eval] k <= hi
(pop) ; 6
(push) ; 6
; [else-branch: 19 | !(k@48@15 >= i@39@15 + 1)]
(assert (not (>= k@48@15 (+ i@39@15 1))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@48@15 (+ i@39@15 1))) (>= k@48@15 (+ i@39@15 1))))
(push) ; 5
; [then-branch: 20 | k@48@15 <= hi@7@15 && k@48@15 >= i@39@15 + 1 | live]
; [else-branch: 20 | !(k@48@15 <= hi@7@15 && k@48@15 >= i@39@15 + 1) | live]
(push) ; 6
; [then-branch: 20 | k@48@15 <= hi@7@15 && k@48@15 >= i@39@15 + 1]
(assert (and (<= k@48@15 hi@7@15) (>= k@48@15 (+ i@39@15 1))))
; [eval] slot(a, k).val > slot(a, i).val
; [eval] slot(a, k)
(declare-const sm@49@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@49@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@49@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef17|)))
(declare-const pm@50@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@50@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@50@15  $FPM) r))
  :qid |qp.resPrmSumDef18|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@50@15  $FPM) (slot<Ref> a@5@15 k@48@15)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [eval] slot(a, i)
(declare-const sm@51@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@51@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@51@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef19|)))
(declare-const pm@52@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@52@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@52@15  $FPM) r))
  :qid |qp.resPrmSumDef20|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@52@15  $FPM) (slot<Ref> a@5@15 i@39@15)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 20 | !(k@48@15 <= hi@7@15 && k@48@15 >= i@39@15 + 1)]
(assert (not (and (<= k@48@15 hi@7@15) (>= k@48@15 (+ i@39@15 1)))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@49@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@49@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef17|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@50@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@50@15  $FPM) r))
  :qid |qp.resPrmSumDef18|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@51@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@51@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef19|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@52@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@52@15  $FPM) r))
  :qid |qp.resPrmSumDef20|)))
; Joined path conditions
(assert (or
  (not (and (<= k@48@15 hi@7@15) (>= k@48@15 (+ i@39@15 1))))
  (and (<= k@48@15 hi@7@15) (>= k@48@15 (+ i@39@15 1)))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@49@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@49@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef17|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@50@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@50@15  $FPM) r))
  :qid |qp.resPrmSumDef18|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@51@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@51@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef19|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@52@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@52@15  $FPM) r))
  :qid |qp.resPrmSumDef20|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@48@15 Int)) (!
  (and
    (or (not (>= k@48@15 (+ i@39@15 1))) (>= k@48@15 (+ i@39@15 1)))
    (or
      (not (and (<= k@48@15 hi@7@15) (>= k@48@15 (+ i@39@15 1))))
      (and (<= k@48@15 hi@7@15) (>= k@48@15 (+ i@39@15 1)))))
  :pattern ((slot<Ref> a@5@15 k@48@15))
  :qid |prog.l40-aux|)))
(assert (forall ((k@48@15 Int)) (!
  (=>
    (and (<= k@48@15 hi@7@15) (>= k@48@15 (+ i@39@15 1)))
    (>
      ($FVF.lookup_val (as sm@49@15  $FVF<val>) (slot<Ref> a@5@15 k@48@15))
      ($FVF.lookup_val (as sm@51@15  $FVF<val>) (slot<Ref> a@5@15 i@39@15))))
  :pattern ((slot<Ref> a@5@15 k@48@15))
  :qid |prog.l40|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15)))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15)))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15))))))
  $Snap.unit))
; [eval] (forall k$1: Int :: { slot(a, k$1) } 0 <= k$1 && k$1 <= lo - 1 ==> slot(a, k$1).val == old(slot(a, k$1).val))
(declare-const k$1@53@15 Int)
(push) ; 4
; [eval] 0 <= k$1 && k$1 <= lo - 1 ==> slot(a, k$1).val == old(slot(a, k$1).val)
; [eval] 0 <= k$1 && k$1 <= lo - 1
; [eval] 0 <= k$1
(push) ; 5
; [then-branch: 21 | 0 <= k$1@53@15 | live]
; [else-branch: 21 | !(0 <= k$1@53@15) | live]
(push) ; 6
; [then-branch: 21 | 0 <= k$1@53@15]
(assert (<= 0 k$1@53@15))
; [eval] k$1 <= lo - 1
; [eval] lo - 1
(pop) ; 6
(push) ; 6
; [else-branch: 21 | !(0 <= k$1@53@15)]
(assert (not (<= 0 k$1@53@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 k$1@53@15)) (<= 0 k$1@53@15)))
(push) ; 5
; [then-branch: 22 | k$1@53@15 <= lo@6@15 - 1 && 0 <= k$1@53@15 | live]
; [else-branch: 22 | !(k$1@53@15 <= lo@6@15 - 1 && 0 <= k$1@53@15) | live]
(push) ; 6
; [then-branch: 22 | k$1@53@15 <= lo@6@15 - 1 && 0 <= k$1@53@15]
(assert (and (<= k$1@53@15 (- lo@6@15 1)) (<= 0 k$1@53@15)))
; [eval] slot(a, k$1).val == old(slot(a, k$1).val)
; [eval] slot(a, k$1)
(declare-const sm@54@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@54@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@54@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef21|)))
(declare-const pm@55@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@55@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@55@15  $FPM) r))
  :qid |qp.resPrmSumDef22|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@55@15  $FPM) (slot<Ref> a@5@15 k$1@53@15)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$1).val)
; [eval] slot(a, k$1)
(push) ; 7
(assert (not (and
  (< (inv@12@15 (slot<Ref> a@5@15 k$1@53@15)) (len<Int> a@5@15))
  (<= 0 (inv@12@15 (slot<Ref> a@5@15 k$1@53@15))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 22 | !(k$1@53@15 <= lo@6@15 - 1 && 0 <= k$1@53@15)]
(assert (not (and (<= k$1@53@15 (- lo@6@15 1)) (<= 0 k$1@53@15))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@54@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@54@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef21|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@55@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@55@15  $FPM) r))
  :qid |qp.resPrmSumDef22|)))
; Joined path conditions
(assert (or
  (not (and (<= k$1@53@15 (- lo@6@15 1)) (<= 0 k$1@53@15)))
  (and (<= k$1@53@15 (- lo@6@15 1)) (<= 0 k$1@53@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@54@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@54@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef21|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@55@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@55@15  $FPM) r))
  :qid |qp.resPrmSumDef22|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$1@53@15 Int)) (!
  (and
    (or (not (<= 0 k$1@53@15)) (<= 0 k$1@53@15))
    (or
      (not (and (<= k$1@53@15 (- lo@6@15 1)) (<= 0 k$1@53@15)))
      (and (<= k$1@53@15 (- lo@6@15 1)) (<= 0 k$1@53@15))))
  :pattern ((slot<Ref> a@5@15 k$1@53@15))
  :qid |prog.l41-aux|)))
(assert (forall ((k$1@53@15 Int)) (!
  (=>
    (and (<= k$1@53@15 (- lo@6@15 1)) (<= 0 k$1@53@15))
    (=
      ($FVF.lookup_val (as sm@54@15  $FVF<val>) (slot<Ref> a@5@15 k$1@53@15))
      ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$1@53@15))))
  :pattern ((slot<Ref> a@5@15 k$1@53@15))
  :qid |prog.l41|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15)))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15)))))))
  $Snap.unit))
; [eval] (forall k$2: Int :: { slot(a, k$2) } hi + 1 <= k$2 && k$2 <= len(a) - 1 ==> slot(a, k$2).val == old(slot(a, k$2).val))
(declare-const k$2@56@15 Int)
(push) ; 4
; [eval] hi + 1 <= k$2 && k$2 <= len(a) - 1 ==> slot(a, k$2).val == old(slot(a, k$2).val)
; [eval] hi + 1 <= k$2 && k$2 <= len(a) - 1
; [eval] hi + 1 <= k$2
; [eval] hi + 1
(push) ; 5
; [then-branch: 23 | hi@7@15 + 1 <= k$2@56@15 | live]
; [else-branch: 23 | !(hi@7@15 + 1 <= k$2@56@15) | live]
(push) ; 6
; [then-branch: 23 | hi@7@15 + 1 <= k$2@56@15]
(assert (<= (+ hi@7@15 1) k$2@56@15))
; [eval] k$2 <= len(a) - 1
; [eval] len(a) - 1
; [eval] len(a)
(pop) ; 6
(push) ; 6
; [else-branch: 23 | !(hi@7@15 + 1 <= k$2@56@15)]
(assert (not (<= (+ hi@7@15 1) k$2@56@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= (+ hi@7@15 1) k$2@56@15)) (<= (+ hi@7@15 1) k$2@56@15)))
(push) ; 5
; [then-branch: 24 | k$2@56@15 <= len[Int](a@5@15) - 1 && hi@7@15 + 1 <= k$2@56@15 | live]
; [else-branch: 24 | !(k$2@56@15 <= len[Int](a@5@15) - 1 && hi@7@15 + 1 <= k$2@56@15) | live]
(push) ; 6
; [then-branch: 24 | k$2@56@15 <= len[Int](a@5@15) - 1 && hi@7@15 + 1 <= k$2@56@15]
(assert (and (<= k$2@56@15 (- (len<Int> a@5@15) 1)) (<= (+ hi@7@15 1) k$2@56@15)))
; [eval] slot(a, k$2).val == old(slot(a, k$2).val)
; [eval] slot(a, k$2)
(declare-const sm@57@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@57@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@57@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef23|)))
(declare-const pm@58@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@58@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@58@15  $FPM) r))
  :qid |qp.resPrmSumDef24|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@58@15  $FPM) (slot<Ref> a@5@15 k$2@56@15)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$2).val)
; [eval] slot(a, k$2)
(push) ; 7
(assert (not (and
  (< (inv@12@15 (slot<Ref> a@5@15 k$2@56@15)) (len<Int> a@5@15))
  (<= 0 (inv@12@15 (slot<Ref> a@5@15 k$2@56@15))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 24 | !(k$2@56@15 <= len[Int](a@5@15) - 1 && hi@7@15 + 1 <= k$2@56@15)]
(assert (not (and (<= k$2@56@15 (- (len<Int> a@5@15) 1)) (<= (+ hi@7@15 1) k$2@56@15))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@57@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@57@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef23|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@58@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@58@15  $FPM) r))
  :qid |qp.resPrmSumDef24|)))
; Joined path conditions
(assert (or
  (not (and (<= k$2@56@15 (- (len<Int> a@5@15) 1)) (<= (+ hi@7@15 1) k$2@56@15)))
  (and (<= k$2@56@15 (- (len<Int> a@5@15) 1)) (<= (+ hi@7@15 1) k$2@56@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@57@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@57@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef23|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@58@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@58@15  $FPM) r))
  :qid |qp.resPrmSumDef24|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$2@56@15 Int)) (!
  (and
    (or (not (<= (+ hi@7@15 1) k$2@56@15)) (<= (+ hi@7@15 1) k$2@56@15))
    (or
      (not
        (and (<= k$2@56@15 (- (len<Int> a@5@15) 1)) (<= (+ hi@7@15 1) k$2@56@15)))
      (and (<= k$2@56@15 (- (len<Int> a@5@15) 1)) (<= (+ hi@7@15 1) k$2@56@15))))
  :pattern ((slot<Ref> a@5@15 k$2@56@15))
  :qid |prog.l42-aux|)))
(assert (forall ((k$2@56@15 Int)) (!
  (=>
    (and (<= k$2@56@15 (- (len<Int> a@5@15) 1)) (<= (+ hi@7@15 1) k$2@56@15))
    (=
      ($FVF.lookup_val (as sm@57@15  $FVF<val>) (slot<Ref> a@5@15 k$2@56@15))
      ($FVF.lookup_val (as sm@37@15  $FVF<val>) (slot<Ref> a@5@15 k$2@56@15))))
  :pattern ((slot<Ref> a@5@15 k$2@56@15))
  :qid |prog.l42|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@40@15)))))))
  $Snap.unit))
; [eval] (forall k$3: Int :: { slot(a, k$3) } lo <= k$3 && k$3 <= hi ==> lb <= slot(a, k$3).val && slot(a, k$3).val <= rb)
(declare-const k$3@59@15 Int)
(push) ; 4
; [eval] lo <= k$3 && k$3 <= hi ==> lb <= slot(a, k$3).val && slot(a, k$3).val <= rb
; [eval] lo <= k$3 && k$3 <= hi
; [eval] lo <= k$3
(push) ; 5
; [then-branch: 25 | lo@6@15 <= k$3@59@15 | live]
; [else-branch: 25 | !(lo@6@15 <= k$3@59@15) | live]
(push) ; 6
; [then-branch: 25 | lo@6@15 <= k$3@59@15]
(assert (<= lo@6@15 k$3@59@15))
; [eval] k$3 <= hi
(pop) ; 6
(push) ; 6
; [else-branch: 25 | !(lo@6@15 <= k$3@59@15)]
(assert (not (<= lo@6@15 k$3@59@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@6@15 k$3@59@15)) (<= lo@6@15 k$3@59@15)))
(push) ; 5
; [then-branch: 26 | k$3@59@15 <= hi@7@15 && lo@6@15 <= k$3@59@15 | live]
; [else-branch: 26 | !(k$3@59@15 <= hi@7@15 && lo@6@15 <= k$3@59@15) | live]
(push) ; 6
; [then-branch: 26 | k$3@59@15 <= hi@7@15 && lo@6@15 <= k$3@59@15]
(assert (and (<= k$3@59@15 hi@7@15) (<= lo@6@15 k$3@59@15)))
; [eval] lb <= slot(a, k$3).val && slot(a, k$3).val <= rb
; [eval] lb <= slot(a, k$3).val
; [eval] slot(a, k$3)
(declare-const sm@60@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@60@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@60@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef25|)))
(declare-const pm@61@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@61@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@61@15  $FPM) r))
  :qid |qp.resPrmSumDef26|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@61@15  $FPM) (slot<Ref> a@5@15 k$3@59@15)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch: 27 | lb@8@15 <= Lookup(val,sm@60@15,slot[Ref](a@5@15, k$3@59@15)) | live]
; [else-branch: 27 | !(lb@8@15 <= Lookup(val,sm@60@15,slot[Ref](a@5@15, k$3@59@15))) | live]
(push) ; 8
; [then-branch: 27 | lb@8@15 <= Lookup(val,sm@60@15,slot[Ref](a@5@15, k$3@59@15))]
(assert (<=
  lb@8@15
  ($FVF.lookup_val (as sm@60@15  $FVF<val>) (slot<Ref> a@5@15 k$3@59@15))))
; [eval] slot(a, k$3).val <= rb
; [eval] slot(a, k$3)
(declare-const sm@62@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@62@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@62@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef27|)))
(declare-const pm@63@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@63@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@63@15  $FPM) r))
  :qid |qp.resPrmSumDef28|)))
(push) ; 9
(assert (not (< $Perm.No ($FVF.perm_val (as pm@63@15  $FPM) (slot<Ref> a@5@15 k$3@59@15)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 27 | !(lb@8@15 <= Lookup(val,sm@60@15,slot[Ref](a@5@15, k$3@59@15)))]
(assert (not
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@60@15  $FVF<val>) (slot<Ref> a@5@15 k$3@59@15)))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@62@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@62@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef27|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@63@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@63@15  $FPM) r))
  :qid |qp.resPrmSumDef28|)))
; Joined path conditions
(assert (or
  (not
    (<=
      lb@8@15
      ($FVF.lookup_val (as sm@60@15  $FVF<val>) (slot<Ref> a@5@15 k$3@59@15))))
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@60@15  $FVF<val>) (slot<Ref> a@5@15 k$3@59@15)))))
(pop) ; 6
(push) ; 6
; [else-branch: 26 | !(k$3@59@15 <= hi@7@15 && lo@6@15 <= k$3@59@15)]
(assert (not (and (<= k$3@59@15 hi@7@15) (<= lo@6@15 k$3@59@15))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@60@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@60@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef25|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@61@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@61@15  $FPM) r))
  :qid |qp.resPrmSumDef26|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@62@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@62@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef27|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@63@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@63@15  $FPM) r))
  :qid |qp.resPrmSumDef28|)))
(assert (=>
  (and (<= k$3@59@15 hi@7@15) (<= lo@6@15 k$3@59@15))
  (and
    (<= k$3@59@15 hi@7@15)
    (<= lo@6@15 k$3@59@15)
    (or
      (not
        (<=
          lb@8@15
          ($FVF.lookup_val (as sm@60@15  $FVF<val>) (slot<Ref> a@5@15 k$3@59@15))))
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@60@15  $FVF<val>) (slot<Ref> a@5@15 k$3@59@15)))))))
; Joined path conditions
(assert (or
  (not (and (<= k$3@59@15 hi@7@15) (<= lo@6@15 k$3@59@15)))
  (and (<= k$3@59@15 hi@7@15) (<= lo@6@15 k$3@59@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@60@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@60@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef25|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@61@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@61@15  $FPM) r))
  :qid |qp.resPrmSumDef26|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@62@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@62@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef27|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@63@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@63@15  $FPM) r))
  :qid |qp.resPrmSumDef28|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$3@59@15 Int)) (!
  (and
    (or (not (<= lo@6@15 k$3@59@15)) (<= lo@6@15 k$3@59@15))
    (=>
      (and (<= k$3@59@15 hi@7@15) (<= lo@6@15 k$3@59@15))
      (and
        (<= k$3@59@15 hi@7@15)
        (<= lo@6@15 k$3@59@15)
        (or
          (not
            (<=
              lb@8@15
              ($FVF.lookup_val (as sm@60@15  $FVF<val>) (slot<Ref> a@5@15 k$3@59@15))))
          (<=
            lb@8@15
            ($FVF.lookup_val (as sm@60@15  $FVF<val>) (slot<Ref> a@5@15 k$3@59@15))))))
    (or
      (not (and (<= k$3@59@15 hi@7@15) (<= lo@6@15 k$3@59@15)))
      (and (<= k$3@59@15 hi@7@15) (<= lo@6@15 k$3@59@15))))
  :pattern ((slot<Ref> a@5@15 k$3@59@15))
  :qid |prog.l43-aux|)))
(assert (forall ((k$3@59@15 Int)) (!
  (=>
    (and (<= k$3@59@15 hi@7@15) (<= lo@6@15 k$3@59@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@62@15  $FVF<val>) (slot<Ref> a@5@15 k$3@59@15))
        rb@9@15)
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@60@15  $FVF<val>) (slot<Ref> a@5@15 k$3@59@15)))))
  :pattern ((slot<Ref> a@5@15 k$3@59@15))
  :qid |prog.l43|)))
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
; [exec]
; pivot := slot(a, p).val
; [eval] slot(a, p)
(declare-const sm@64@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@64@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@64@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef29|)))
(declare-const pm@65@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@65@15  $FPM) r)
    (ite
      (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@65@15  $FPM) r))
  :qid |qp.resPrmSumDef30|)))
(set-option :timeout 0)
(push) ; 4
(assert (not (< $Perm.No ($FVF.perm_val (as pm@65@15  $FPM) (slot<Ref> a@5@15 i@39@15)))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(declare-const pivot@66@15 Int)
(assert (=
  pivot@66@15
  ($FVF.lookup_val (as sm@64@15  $FVF<val>) (slot<Ref> a@5@15 i@39@15))))
; [exec]
; quicksort(a, lo, p - 1, lb, pivot)
; [eval] p - 1
(declare-const j$0@67@15 Int)
(push) ; 4
; [eval] 0 <= j$0 && j$0 < len(a)
; [eval] 0 <= j$0
(push) ; 5
; [then-branch: 28 | 0 <= j$0@67@15 | live]
; [else-branch: 28 | !(0 <= j$0@67@15) | live]
(push) ; 6
; [then-branch: 28 | 0 <= j$0@67@15]
(assert (<= 0 j$0@67@15))
; [eval] j$0 < len(a)
; [eval] len(a)
(pop) ; 6
(push) ; 6
; [else-branch: 28 | !(0 <= j$0@67@15)]
(assert (not (<= 0 j$0@67@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$0@67@15)) (<= 0 j$0@67@15)))
(assert (and (< j$0@67@15 (len<Int> a@5@15)) (<= 0 j$0@67@15)))
; [eval] slot(a, j$0)
(pop) ; 4
(declare-fun inv@68@15 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$0@67@15 Int)) (!
  (=>
    (and (< j$0@67@15 (len<Int> a@5@15)) (<= 0 j$0@67@15))
    (or (not (<= 0 j$0@67@15)) (<= 0 j$0@67@15)))
  :pattern ((slot<Ref> a@5@15 j$0@67@15))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 4
(assert (not (forall ((j$01@67@15 Int) (j$02@67@15 Int)) (!
  (=>
    (and
      (and (< j$01@67@15 (len<Int> a@5@15)) (<= 0 j$01@67@15))
      (and (< j$02@67@15 (len<Int> a@5@15)) (<= 0 j$02@67@15))
      (= (slot<Ref> a@5@15 j$01@67@15) (slot<Ref> a@5@15 j$02@67@15)))
    (= j$01@67@15 j$02@67@15))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$0@67@15 Int)) (!
  (=>
    (and (< j$0@67@15 (len<Int> a@5@15)) (<= 0 j$0@67@15))
    (= (inv@68@15 (slot<Ref> a@5@15 j$0@67@15)) j$0@67@15))
  :pattern ((slot<Ref> a@5@15 j$0@67@15))
  :qid |val-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@68@15 r) (len<Int> a@5@15)) (<= 0 (inv@68@15 r)))
    (= (slot<Ref> a@5@15 (inv@68@15 r)) r))
  :pattern ((inv@68@15 r))
  :qid |val-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@69@15 ((r $Ref)) $Perm
  (ite
    (and (< (inv@68@15 r) (len<Int> a@5@15)) (<= 0 (inv@68@15 r)))
    ($Perm.min
      (ite
        (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Chunk depleted?
(set-option :timeout 0)
(push) ; 4
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (ite
        (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
        $Perm.Write
        $Perm.No)
      (pTaken@69@15 r))
    $Perm.No)
  
  :qid |quant-u-18|))))
(check-sat)
; unsat
(pop) ; 4
; 0.01s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 4
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (and (< (inv@68@15 r) (len<Int> a@5@15)) (<= 0 (inv@68@15 r)))
    (= (- $Perm.Write (pTaken@69@15 r)) $Perm.No))
  
  :qid |quant-u-19|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@70@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@42@15 r) (len<Int> a@5@15)) (<= 0 (inv@42@15 r)))
    (=
      ($FVF.lookup_val (as sm@70@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r)))
  :pattern (($FVF.lookup_val (as sm@70@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@40@15)) r))
  :qid |qp.fvfValDef31|)))
; [eval] lo >= 0
; [eval] hi < len(a)
; [eval] len(a)
(set-option :timeout 0)
(push) ; 4
(assert (not (< (- i@39@15 1) (len<Int> a@5@15))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (< (- i@39@15 1) (len<Int> a@5@15)))
; [eval] hi >= -1
; [eval] -1
(push) ; 4
(assert (not (>= (- i@39@15 1) (- 0 1))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (>= (- i@39@15 1) (- 0 1)))
; [eval] lo <= len(a)
; [eval] len(a)
; [eval] (forall k: Int :: { slot(a, k) } lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb)
(declare-const k@71@15 Int)
(push) ; 4
; [eval] lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lo <= k && k <= hi
; [eval] lo <= k
(push) ; 5
; [then-branch: 29 | lo@6@15 <= k@71@15 | live]
; [else-branch: 29 | !(lo@6@15 <= k@71@15) | live]
(push) ; 6
; [then-branch: 29 | lo@6@15 <= k@71@15]
(assert (<= lo@6@15 k@71@15))
; [eval] k <= hi
(pop) ; 6
(push) ; 6
; [else-branch: 29 | !(lo@6@15 <= k@71@15)]
(assert (not (<= lo@6@15 k@71@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@6@15 k@71@15)) (<= lo@6@15 k@71@15)))
(push) ; 5
; [then-branch: 30 | k@71@15 <= i@39@15 - 1 && lo@6@15 <= k@71@15 | live]
; [else-branch: 30 | !(k@71@15 <= i@39@15 - 1 && lo@6@15 <= k@71@15) | live]
(push) ; 6
; [then-branch: 30 | k@71@15 <= i@39@15 - 1 && lo@6@15 <= k@71@15]
(assert (and (<= k@71@15 (- i@39@15 1)) (<= lo@6@15 k@71@15)))
; [eval] lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lb <= slot(a, k).val
; [eval] slot(a, k)
(push) ; 7
(assert (not (and
  (< (inv@42@15 (slot<Ref> a@5@15 k@71@15)) (len<Int> a@5@15))
  (<= 0 (inv@42@15 (slot<Ref> a@5@15 k@71@15))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch: 31 | lb@8@15 <= Lookup(val,sm@70@15,slot[Ref](a@5@15, k@71@15)) | live]
; [else-branch: 31 | !(lb@8@15 <= Lookup(val,sm@70@15,slot[Ref](a@5@15, k@71@15))) | live]
(push) ; 8
; [then-branch: 31 | lb@8@15 <= Lookup(val,sm@70@15,slot[Ref](a@5@15, k@71@15))]
(assert (<=
  lb@8@15
  ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15))))
; [eval] slot(a, k).val <= rb
; [eval] slot(a, k)
(push) ; 9
(assert (not (and
  (< (inv@42@15 (slot<Ref> a@5@15 k@71@15)) (len<Int> a@5@15))
  (<= 0 (inv@42@15 (slot<Ref> a@5@15 k@71@15))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 31 | !(lb@8@15 <= Lookup(val,sm@70@15,slot[Ref](a@5@15, k@71@15)))]
(assert (not
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15)))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (<=
      lb@8@15
      ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15))))
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15)))))
(pop) ; 6
(push) ; 6
; [else-branch: 30 | !(k@71@15 <= i@39@15 - 1 && lo@6@15 <= k@71@15)]
(assert (not (and (<= k@71@15 (- i@39@15 1)) (<= lo@6@15 k@71@15))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (=>
  (and (<= k@71@15 (- i@39@15 1)) (<= lo@6@15 k@71@15))
  (and
    (<= k@71@15 (- i@39@15 1))
    (<= lo@6@15 k@71@15)
    (or
      (not
        (<=
          lb@8@15
          ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15))))
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15)))))))
; Joined path conditions
(assert (or
  (not (and (<= k@71@15 (- i@39@15 1)) (<= lo@6@15 k@71@15)))
  (and (<= k@71@15 (- i@39@15 1)) (<= lo@6@15 k@71@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@71@15 Int)) (!
  (and
    (or (not (<= lo@6@15 k@71@15)) (<= lo@6@15 k@71@15))
    (=>
      (and (<= k@71@15 (- i@39@15 1)) (<= lo@6@15 k@71@15))
      (and
        (<= k@71@15 (- i@39@15 1))
        (<= lo@6@15 k@71@15)
        (or
          (not
            (<=
              lb@8@15
              ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15))))
          (<=
            lb@8@15
            ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15))))))
    (or
      (not (and (<= k@71@15 (- i@39@15 1)) (<= lo@6@15 k@71@15)))
      (and (<= k@71@15 (- i@39@15 1)) (<= lo@6@15 k@71@15))))
  :pattern ((slot<Ref> a@5@15 k@71@15))
  :qid |prog.l81-aux|)))
(push) ; 4
(assert (not (forall ((k@71@15 Int)) (!
  (=>
    (and (<= k@71@15 (- i@39@15 1)) (<= lo@6@15 k@71@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15))
        pivot@66@15)
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15)))))
  :pattern ((slot<Ref> a@5@15 k@71@15))
  :qid |prog.l81|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@71@15 Int)) (!
  (=>
    (and (<= k@71@15 (- i@39@15 1)) (<= lo@6@15 k@71@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15))
        pivot@66@15)
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@70@15  $FVF<val>) (slot<Ref> a@5@15 k@71@15)))))
  :pattern ((slot<Ref> a@5@15 k@71@15))
  :qid |prog.l81|)))
; [eval] lb <= rb
(push) ; 4
(assert (not (<= lb@8@15 pivot@66@15)))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (<= lb@8@15 pivot@66@15))
(declare-const $t@72@15 $Snap)
(assert (= $t@72@15 ($Snap.combine ($Snap.first $t@72@15) ($Snap.second $t@72@15))))
(declare-const j$1@73@15 Int)
(push) ; 4
; [eval] 0 <= j$1 && j$1 < len(a)
; [eval] 0 <= j$1
(push) ; 5
; [then-branch: 32 | 0 <= j$1@73@15 | live]
; [else-branch: 32 | !(0 <= j$1@73@15) | live]
(push) ; 6
; [then-branch: 32 | 0 <= j$1@73@15]
(assert (<= 0 j$1@73@15))
; [eval] j$1 < len(a)
; [eval] len(a)
(pop) ; 6
(push) ; 6
; [else-branch: 32 | !(0 <= j$1@73@15)]
(assert (not (<= 0 j$1@73@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$1@73@15)) (<= 0 j$1@73@15)))
(assert (and (< j$1@73@15 (len<Int> a@5@15)) (<= 0 j$1@73@15)))
; [eval] slot(a, j$1)
(pop) ; 4
(declare-fun inv@74@15 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$1@73@15 Int)) (!
  (=>
    (and (< j$1@73@15 (len<Int> a@5@15)) (<= 0 j$1@73@15))
    (or (not (<= 0 j$1@73@15)) (<= 0 j$1@73@15)))
  :pattern ((slot<Ref> a@5@15 j$1@73@15))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 4
(assert (not (forall ((j$11@73@15 Int) (j$12@73@15 Int)) (!
  (=>
    (and
      (and (< j$11@73@15 (len<Int> a@5@15)) (<= 0 j$11@73@15))
      (and (< j$12@73@15 (len<Int> a@5@15)) (<= 0 j$12@73@15))
      (= (slot<Ref> a@5@15 j$11@73@15) (slot<Ref> a@5@15 j$12@73@15)))
    (= j$11@73@15 j$12@73@15))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$1@73@15 Int)) (!
  (=>
    (and (< j$1@73@15 (len<Int> a@5@15)) (<= 0 j$1@73@15))
    (= (inv@74@15 (slot<Ref> a@5@15 j$1@73@15)) j$1@73@15))
  :pattern ((slot<Ref> a@5@15 j$1@73@15))
  :qid |quant-u-25|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (= (slot<Ref> a@5@15 (inv@74@15 r)) r))
  :pattern ((inv@74@15 r))
  :qid |val-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j$1@73@15 Int)) (!
  (=>
    (and (< j$1@73@15 (len<Int> a@5@15)) (<= 0 j$1@73@15))
    (not (= (slot<Ref> a@5@15 j$1@73@15) $Ref.null)))
  :pattern ((slot<Ref> a@5@15 j$1@73@15))
  :qid |val-permImpliesNonNull|)))
(assert (=
  ($Snap.second $t@72@15)
  ($Snap.combine
    ($Snap.first ($Snap.second $t@72@15))
    ($Snap.second ($Snap.second $t@72@15)))))
(assert (= ($Snap.first ($Snap.second $t@72@15)) $Snap.unit))
; [eval] (forall k$0: Int :: { slot(a, k$0) } lo <= k$0 && k$0 <= hi ==> lb <= slot(a, k$0).val && slot(a, k$0).val <= rb)
(declare-const k$0@75@15 Int)
(push) ; 4
; [eval] lo <= k$0 && k$0 <= hi ==> lb <= slot(a, k$0).val && slot(a, k$0).val <= rb
; [eval] lo <= k$0 && k$0 <= hi
; [eval] lo <= k$0
(push) ; 5
; [then-branch: 33 | lo@6@15 <= k$0@75@15 | live]
; [else-branch: 33 | !(lo@6@15 <= k$0@75@15) | live]
(push) ; 6
; [then-branch: 33 | lo@6@15 <= k$0@75@15]
(assert (<= lo@6@15 k$0@75@15))
; [eval] k$0 <= hi
(pop) ; 6
(push) ; 6
; [else-branch: 33 | !(lo@6@15 <= k$0@75@15)]
(assert (not (<= lo@6@15 k$0@75@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@6@15 k$0@75@15)) (<= lo@6@15 k$0@75@15)))
(push) ; 5
; [then-branch: 34 | k$0@75@15 <= i@39@15 - 1 && lo@6@15 <= k$0@75@15 | live]
; [else-branch: 34 | !(k$0@75@15 <= i@39@15 - 1 && lo@6@15 <= k$0@75@15) | live]
(push) ; 6
; [then-branch: 34 | k$0@75@15 <= i@39@15 - 1 && lo@6@15 <= k$0@75@15]
(assert (and (<= k$0@75@15 (- i@39@15 1)) (<= lo@6@15 k$0@75@15)))
; [eval] lb <= slot(a, k$0).val && slot(a, k$0).val <= rb
; [eval] lb <= slot(a, k$0).val
; [eval] slot(a, k$0)
(declare-const sm@76@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@76@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@76@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef32|)))
(declare-const pm@77@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@77@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@77@15  $FPM) r))
  :qid |qp.resPrmSumDef33|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@77@15  $FPM) (slot<Ref> a@5@15 k$0@75@15)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch: 35 | lb@8@15 <= Lookup(val,sm@76@15,slot[Ref](a@5@15, k$0@75@15)) | live]
; [else-branch: 35 | !(lb@8@15 <= Lookup(val,sm@76@15,slot[Ref](a@5@15, k$0@75@15))) | live]
(push) ; 8
; [then-branch: 35 | lb@8@15 <= Lookup(val,sm@76@15,slot[Ref](a@5@15, k$0@75@15))]
(assert (<=
  lb@8@15
  ($FVF.lookup_val (as sm@76@15  $FVF<val>) (slot<Ref> a@5@15 k$0@75@15))))
; [eval] slot(a, k$0).val <= rb
; [eval] slot(a, k$0)
(declare-const sm@78@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@78@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@78@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef34|)))
(declare-const pm@79@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@79@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@79@15  $FPM) r))
  :qid |qp.resPrmSumDef35|)))
(push) ; 9
(assert (not (< $Perm.No ($FVF.perm_val (as pm@79@15  $FPM) (slot<Ref> a@5@15 k$0@75@15)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 35 | !(lb@8@15 <= Lookup(val,sm@76@15,slot[Ref](a@5@15, k$0@75@15)))]
(assert (not
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@76@15  $FVF<val>) (slot<Ref> a@5@15 k$0@75@15)))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@78@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@78@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef34|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@79@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@79@15  $FPM) r))
  :qid |qp.resPrmSumDef35|)))
; Joined path conditions
(assert (or
  (not
    (<=
      lb@8@15
      ($FVF.lookup_val (as sm@76@15  $FVF<val>) (slot<Ref> a@5@15 k$0@75@15))))
  (<=
    lb@8@15
    ($FVF.lookup_val (as sm@76@15  $FVF<val>) (slot<Ref> a@5@15 k$0@75@15)))))
(pop) ; 6
(push) ; 6
; [else-branch: 34 | !(k$0@75@15 <= i@39@15 - 1 && lo@6@15 <= k$0@75@15)]
(assert (not (and (<= k$0@75@15 (- i@39@15 1)) (<= lo@6@15 k$0@75@15))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@76@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@76@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef32|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@77@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@77@15  $FPM) r))
  :qid |qp.resPrmSumDef33|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@78@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@78@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef34|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@79@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@79@15  $FPM) r))
  :qid |qp.resPrmSumDef35|)))
(assert (=>
  (and (<= k$0@75@15 (- i@39@15 1)) (<= lo@6@15 k$0@75@15))
  (and
    (<= k$0@75@15 (- i@39@15 1))
    (<= lo@6@15 k$0@75@15)
    (or
      (not
        (<=
          lb@8@15
          ($FVF.lookup_val (as sm@76@15  $FVF<val>) (slot<Ref> a@5@15 k$0@75@15))))
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@76@15  $FVF<val>) (slot<Ref> a@5@15 k$0@75@15)))))))
; Joined path conditions
(assert (or
  (not (and (<= k$0@75@15 (- i@39@15 1)) (<= lo@6@15 k$0@75@15)))
  (and (<= k$0@75@15 (- i@39@15 1)) (<= lo@6@15 k$0@75@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@76@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@76@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef32|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@77@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@77@15  $FPM) r))
  :qid |qp.resPrmSumDef33|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@78@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@78@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef34|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@79@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@79@15  $FPM) r))
  :qid |qp.resPrmSumDef35|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$0@75@15 Int)) (!
  (and
    (or (not (<= lo@6@15 k$0@75@15)) (<= lo@6@15 k$0@75@15))
    (=>
      (and (<= k$0@75@15 (- i@39@15 1)) (<= lo@6@15 k$0@75@15))
      (and
        (<= k$0@75@15 (- i@39@15 1))
        (<= lo@6@15 k$0@75@15)
        (or
          (not
            (<=
              lb@8@15
              ($FVF.lookup_val (as sm@76@15  $FVF<val>) (slot<Ref> a@5@15 k$0@75@15))))
          (<=
            lb@8@15
            ($FVF.lookup_val (as sm@76@15  $FVF<val>) (slot<Ref> a@5@15 k$0@75@15))))))
    (or
      (not (and (<= k$0@75@15 (- i@39@15 1)) (<= lo@6@15 k$0@75@15)))
      (and (<= k$0@75@15 (- i@39@15 1)) (<= lo@6@15 k$0@75@15))))
  :pattern ((slot<Ref> a@5@15 k$0@75@15))
  :qid |prog.l87-aux|)))
(assert (forall ((k$0@75@15 Int)) (!
  (=>
    (and (<= k$0@75@15 (- i@39@15 1)) (<= lo@6@15 k$0@75@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@78@15  $FVF<val>) (slot<Ref> a@5@15 k$0@75@15))
        pivot@66@15)
      (<=
        lb@8@15
        ($FVF.lookup_val (as sm@76@15  $FVF<val>) (slot<Ref> a@5@15 k$0@75@15)))))
  :pattern ((slot<Ref> a@5@15 k$0@75@15))
  :qid |prog.l87|)))
(assert (= ($Snap.second ($Snap.second $t@72@15)) $Snap.unit))
; [eval] (forall i: Int, j: Int :: { slot(a, i), slot(a, j) } lo <= i && (i <= j && j <= hi) ==> slot(a, i).val <= slot(a, j).val)
(declare-const i@80@15 Int)
(declare-const j@81@15 Int)
(push) ; 4
; [eval] lo <= i && (i <= j && j <= hi) ==> slot(a, i).val <= slot(a, j).val
; [eval] lo <= i && (i <= j && j <= hi)
; [eval] lo <= i
(push) ; 5
; [then-branch: 36 | lo@6@15 <= i@80@15 | live]
; [else-branch: 36 | !(lo@6@15 <= i@80@15) | live]
(push) ; 6
; [then-branch: 36 | lo@6@15 <= i@80@15]
(assert (<= lo@6@15 i@80@15))
; [eval] i <= j
(push) ; 7
; [then-branch: 37 | i@80@15 <= j@81@15 | live]
; [else-branch: 37 | !(i@80@15 <= j@81@15) | live]
(push) ; 8
; [then-branch: 37 | i@80@15 <= j@81@15]
(assert (<= i@80@15 j@81@15))
; [eval] j <= hi
(pop) ; 8
(push) ; 8
; [else-branch: 37 | !(i@80@15 <= j@81@15)]
(assert (not (<= i@80@15 j@81@15)))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or (not (<= i@80@15 j@81@15)) (<= i@80@15 j@81@15)))
(pop) ; 6
(push) ; 6
; [else-branch: 36 | !(lo@6@15 <= i@80@15)]
(assert (not (<= lo@6@15 i@80@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (=>
  (<= lo@6@15 i@80@15)
  (and (<= lo@6@15 i@80@15) (or (not (<= i@80@15 j@81@15)) (<= i@80@15 j@81@15)))))
; Joined path conditions
(assert (or (not (<= lo@6@15 i@80@15)) (<= lo@6@15 i@80@15)))
(push) ; 5
; [then-branch: 38 | j@81@15 <= i@39@15 - 1 && i@80@15 <= j@81@15 && lo@6@15 <= i@80@15 | live]
; [else-branch: 38 | !(j@81@15 <= i@39@15 - 1 && i@80@15 <= j@81@15 && lo@6@15 <= i@80@15) | live]
(push) ; 6
; [then-branch: 38 | j@81@15 <= i@39@15 - 1 && i@80@15 <= j@81@15 && lo@6@15 <= i@80@15]
(assert (and (and (<= j@81@15 (- i@39@15 1)) (<= i@80@15 j@81@15)) (<= lo@6@15 i@80@15)))
; [eval] slot(a, i).val <= slot(a, j).val
; [eval] slot(a, i)
(declare-const sm@82@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@82@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@82@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef36|)))
(declare-const pm@83@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@83@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@83@15  $FPM) r))
  :qid |qp.resPrmSumDef37|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@83@15  $FPM) (slot<Ref> a@5@15 i@80@15)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [eval] slot(a, j)
(declare-const sm@84@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@84@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@84@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef38|)))
(declare-const pm@85@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@85@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@85@15  $FPM) r))
  :qid |qp.resPrmSumDef39|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@85@15  $FPM) (slot<Ref> a@5@15 j@81@15)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 38 | !(j@81@15 <= i@39@15 - 1 && i@80@15 <= j@81@15 && lo@6@15 <= i@80@15)]
(assert (not
  (and
    (and (<= j@81@15 (- i@39@15 1)) (<= i@80@15 j@81@15))
    (<= lo@6@15 i@80@15))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@82@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@82@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef36|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@83@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@83@15  $FPM) r))
  :qid |qp.resPrmSumDef37|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@84@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@84@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef38|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@85@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@85@15  $FPM) r))
  :qid |qp.resPrmSumDef39|)))
(assert (=>
  (and
    (and (<= j@81@15 (- i@39@15 1)) (<= i@80@15 j@81@15))
    (<= lo@6@15 i@80@15))
  (and (<= j@81@15 (- i@39@15 1)) (<= i@80@15 j@81@15) (<= lo@6@15 i@80@15))))
; Joined path conditions
(assert (or
  (not
    (and
      (and (<= j@81@15 (- i@39@15 1)) (<= i@80@15 j@81@15))
      (<= lo@6@15 i@80@15)))
  (and
    (and (<= j@81@15 (- i@39@15 1)) (<= i@80@15 j@81@15))
    (<= lo@6@15 i@80@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@82@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@82@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef36|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@83@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@83@15  $FPM) r))
  :qid |qp.resPrmSumDef37|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@84@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@84@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef38|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@85@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@85@15  $FPM) r))
  :qid |qp.resPrmSumDef39|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((i@80@15 Int) (j@81@15 Int)) (!
  (and
    (=>
      (<= lo@6@15 i@80@15)
      (and
        (<= lo@6@15 i@80@15)
        (or (not (<= i@80@15 j@81@15)) (<= i@80@15 j@81@15))))
    (or (not (<= lo@6@15 i@80@15)) (<= lo@6@15 i@80@15))
    (=>
      (and
        (and (<= j@81@15 (- i@39@15 1)) (<= i@80@15 j@81@15))
        (<= lo@6@15 i@80@15))
      (and (<= j@81@15 (- i@39@15 1)) (<= i@80@15 j@81@15) (<= lo@6@15 i@80@15)))
    (or
      (not
        (and
          (and (<= j@81@15 (- i@39@15 1)) (<= i@80@15 j@81@15))
          (<= lo@6@15 i@80@15)))
      (and
        (and (<= j@81@15 (- i@39@15 1)) (<= i@80@15 j@81@15))
        (<= lo@6@15 i@80@15))))
  :pattern ((slot<Ref> a@5@15 i@80@15) (slot<Ref> a@5@15 j@81@15))
  :qid |prog.l88-aux|)))
(assert (forall ((i@80@15 Int) (j@81@15 Int)) (!
  (=>
    (and
      (and (<= j@81@15 (- i@39@15 1)) (<= i@80@15 j@81@15))
      (<= lo@6@15 i@80@15))
    (<=
      ($FVF.lookup_val (as sm@82@15  $FVF<val>) (slot<Ref> a@5@15 i@80@15))
      ($FVF.lookup_val (as sm@84@15  $FVF<val>) (slot<Ref> a@5@15 j@81@15))))
  :pattern ((slot<Ref> a@5@15 i@80@15) (slot<Ref> a@5@15 j@81@15))
  :qid |prog.l88|)))
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
; [exec]
; quicksort(a, p + 1, hi, pivot, rb)
; [eval] p + 1
(declare-const j$0@86@15 Int)
(set-option :timeout 0)
(push) ; 4
; [eval] 0 <= j$0 && j$0 < len(a)
; [eval] 0 <= j$0
(push) ; 5
; [then-branch: 39 | 0 <= j$0@86@15 | live]
; [else-branch: 39 | !(0 <= j$0@86@15) | live]
(push) ; 6
; [then-branch: 39 | 0 <= j$0@86@15]
(assert (<= 0 j$0@86@15))
; [eval] j$0 < len(a)
; [eval] len(a)
(pop) ; 6
(push) ; 6
; [else-branch: 39 | !(0 <= j$0@86@15)]
(assert (not (<= 0 j$0@86@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$0@86@15)) (<= 0 j$0@86@15)))
(assert (and (< j$0@86@15 (len<Int> a@5@15)) (<= 0 j$0@86@15)))
; [eval] slot(a, j$0)
(pop) ; 4
(declare-fun inv@87@15 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$0@86@15 Int)) (!
  (=>
    (and (< j$0@86@15 (len<Int> a@5@15)) (<= 0 j$0@86@15))
    (or (not (<= 0 j$0@86@15)) (<= 0 j$0@86@15)))
  :pattern ((slot<Ref> a@5@15 j$0@86@15))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 4
(assert (not (forall ((j$01@86@15 Int) (j$02@86@15 Int)) (!
  (=>
    (and
      (and (< j$01@86@15 (len<Int> a@5@15)) (<= 0 j$01@86@15))
      (and (< j$02@86@15 (len<Int> a@5@15)) (<= 0 j$02@86@15))
      (= (slot<Ref> a@5@15 j$01@86@15) (slot<Ref> a@5@15 j$02@86@15)))
    (= j$01@86@15 j$02@86@15))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$0@86@15 Int)) (!
  (=>
    (and (< j$0@86@15 (len<Int> a@5@15)) (<= 0 j$0@86@15))
    (= (inv@87@15 (slot<Ref> a@5@15 j$0@86@15)) j$0@86@15))
  :pattern ((slot<Ref> a@5@15 j$0@86@15))
  :qid |val-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@87@15 r) (len<Int> a@5@15)) (<= 0 (inv@87@15 r)))
    (= (slot<Ref> a@5@15 (inv@87@15 r)) r))
  :pattern ((inv@87@15 r))
  :qid |val-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@88@15 ((r $Ref)) $Perm
  (ite
    (and (< (inv@87@15 r) (len<Int> a@5@15)) (<= 0 (inv@87@15 r)))
    ($Perm.min
      (ite
        (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Chunk depleted?
(set-option :timeout 0)
(push) ; 4
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (ite
        (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
        $Perm.Write
        $Perm.No)
      (pTaken@88@15 r))
    $Perm.No)
  
  :qid |quant-u-28|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 4
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (and (< (inv@87@15 r) (len<Int> a@5@15)) (<= 0 (inv@87@15 r)))
    (= (- $Perm.Write (pTaken@88@15 r)) $Perm.No))
  
  :qid |quant-u-29|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@89@15 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
    (=
      ($FVF.lookup_val (as sm@89@15  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r)))
  :pattern (($FVF.lookup_val (as sm@89@15  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@72@15)) r))
  :qid |qp.fvfValDef40|)))
; [eval] lo >= 0
(set-option :timeout 0)
(push) ; 4
(assert (not (>= (+ i@39@15 1) 0)))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (>= (+ i@39@15 1) 0))
; [eval] hi < len(a)
; [eval] len(a)
; [eval] hi >= -1
; [eval] -1
; [eval] lo <= len(a)
; [eval] len(a)
(push) ; 4
(assert (not (<= (+ i@39@15 1) (len<Int> a@5@15))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (<= (+ i@39@15 1) (len<Int> a@5@15)))
; [eval] (forall k: Int :: { slot(a, k) } lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb)
(declare-const k@90@15 Int)
(push) ; 4
; [eval] lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lo <= k && k <= hi
; [eval] lo <= k
(push) ; 5
; [then-branch: 40 | i@39@15 + 1 <= k@90@15 | live]
; [else-branch: 40 | !(i@39@15 + 1 <= k@90@15) | live]
(push) ; 6
; [then-branch: 40 | i@39@15 + 1 <= k@90@15]
(assert (<= (+ i@39@15 1) k@90@15))
; [eval] k <= hi
(pop) ; 6
(push) ; 6
; [else-branch: 40 | !(i@39@15 + 1 <= k@90@15)]
(assert (not (<= (+ i@39@15 1) k@90@15)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= (+ i@39@15 1) k@90@15)) (<= (+ i@39@15 1) k@90@15)))
(push) ; 5
; [then-branch: 41 | k@90@15 <= hi@7@15 && i@39@15 + 1 <= k@90@15 | live]
; [else-branch: 41 | !(k@90@15 <= hi@7@15 && i@39@15 + 1 <= k@90@15) | live]
(push) ; 6
; [then-branch: 41 | k@90@15 <= hi@7@15 && i@39@15 + 1 <= k@90@15]
(assert (and (<= k@90@15 hi@7@15) (<= (+ i@39@15 1) k@90@15)))
; [eval] lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lb <= slot(a, k).val
; [eval] slot(a, k)
(push) ; 7
(assert (not (and
  (< (inv@74@15 (slot<Ref> a@5@15 k@90@15)) (len<Int> a@5@15))
  (<= 0 (inv@74@15 (slot<Ref> a@5@15 k@90@15))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch: 42 | pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@90@15)) | live]
; [else-branch: 42 | !(pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@90@15))) | live]
(push) ; 8
; [then-branch: 42 | pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@90@15))]
(assert (<=
  pivot@66@15
  ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@90@15))))
; [eval] slot(a, k).val <= rb
; [eval] slot(a, k)
(push) ; 9
(assert (not (and
  (< (inv@74@15 (slot<Ref> a@5@15 k@90@15)) (len<Int> a@5@15))
  (<= 0 (inv@74@15 (slot<Ref> a@5@15 k@90@15))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 42 | !(pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@90@15)))]
(assert (not
  (<=
    pivot@66@15
    ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@90@15)))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (<=
      pivot@66@15
      ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@90@15))))
  (<=
    pivot@66@15
    ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@90@15)))))
(pop) ; 6
(push) ; 6
; [else-branch: 41 | !(k@90@15 <= hi@7@15 && i@39@15 + 1 <= k@90@15)]
(assert (not (and (<= k@90@15 hi@7@15) (<= (+ i@39@15 1) k@90@15))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (=>
  (and (<= k@90@15 hi@7@15) (<= (+ i@39@15 1) k@90@15))
  (and
    (<= k@90@15 hi@7@15)
    (<= (+ i@39@15 1) k@90@15)
    (or
      (not
        (<=
          pivot@66@15
          ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@90@15))))
      (<=
        pivot@66@15
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@90@15)))))))
; Joined path conditions
(assert (or
  (not (and (<= k@90@15 hi@7@15) (<= (+ i@39@15 1) k@90@15)))
  (and (<= k@90@15 hi@7@15) (<= (+ i@39@15 1) k@90@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@90@15 Int)) (!
  (and
    (or (not (<= (+ i@39@15 1) k@90@15)) (<= (+ i@39@15 1) k@90@15))
    (=>
      (and (<= k@90@15 hi@7@15) (<= (+ i@39@15 1) k@90@15))
      (and
        (<= k@90@15 hi@7@15)
        (<= (+ i@39@15 1) k@90@15)
        (or
          (not
            (<=
              pivot@66@15
              ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@90@15))))
          (<=
            pivot@66@15
            ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@90@15))))))
    (or
      (not (and (<= k@90@15 hi@7@15) (<= (+ i@39@15 1) k@90@15)))
      (and (<= k@90@15 hi@7@15) (<= (+ i@39@15 1) k@90@15))))
  :pattern ((slot<Ref> a@5@15 k@90@15))
  :qid |prog.l81-aux|)))
(push) ; 4
(assert (not (forall ((k@90@15 Int)) (!
  (=>
    (and (<= k@90@15 hi@7@15) (<= (+ i@39@15 1) k@90@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@90@15))
        rb@9@15)
      (<=
        pivot@66@15
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@90@15)))))
  :pattern ((slot<Ref> a@5@15 k@90@15))
  :qid |prog.l81|))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
(declare-const pm@91@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@91@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@91@15  $FPM) r))
  :qid |qp.resPrmSumDef41|)))
; Assume upper permission bound for field val
(assert (forall ((r $Ref)) (!
  (<= ($FVF.perm_val (as pm@91@15  $FPM) r) $Perm.Write)
  :pattern ((inv@74@15 r))
  :qid |qp-fld-prm-bnd|)))
; [eval] (forall k: Int :: { slot(a, k) } lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb)
(declare-const k@92@15 Int)
(set-option :timeout 0)
(push) ; 4
; [eval] lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lo <= k && k <= hi
; [eval] lo <= k
(push) ; 5
; [then-branch: 43 | i@39@15 + 1 <= k@92@15 | live]
; [else-branch: 43 | !(i@39@15 + 1 <= k@92@15) | live]
(push) ; 6
; [then-branch: 43 | i@39@15 + 1 <= k@92@15]
(assert (<= (+ i@39@15 1) k@92@15))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
; [eval] k <= hi
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
; [else-branch: 43 | !(i@39@15 + 1 <= k@92@15)]
(assert (not (<= (+ i@39@15 1) k@92@15)))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= (+ i@39@15 1) k@92@15)) (<= (+ i@39@15 1) k@92@15)))
(set-option :timeout 0)
(push) ; 5
; [then-branch: 44 | k@92@15 <= hi@7@15 && i@39@15 + 1 <= k@92@15 | live]
; [else-branch: 44 | !(k@92@15 <= hi@7@15 && i@39@15 + 1 <= k@92@15) | live]
(push) ; 6
; [then-branch: 44 | k@92@15 <= hi@7@15 && i@39@15 + 1 <= k@92@15]
(assert (and (<= k@92@15 hi@7@15) (<= (+ i@39@15 1) k@92@15)))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
; [eval] lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lb <= slot(a, k).val
; [eval] slot(a, k)
(set-option :timeout 0)
(push) ; 7
(assert (not (and
  (< (inv@74@15 (slot<Ref> a@5@15 k@92@15)) (len<Int> a@5@15))
  (<= 0 (inv@74@15 (slot<Ref> a@5@15 k@92@15))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch: 45 | pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@92@15)) | live]
; [else-branch: 45 | !(pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@92@15))) | live]
(push) ; 8
; [then-branch: 45 | pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@92@15))]
(assert (<=
  pivot@66@15
  ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@92@15))))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
; [eval] slot(a, k).val <= rb
; [eval] slot(a, k)
(set-option :timeout 0)
(push) ; 9
(assert (not (and
  (< (inv@74@15 (slot<Ref> a@5@15 k@92@15)) (len<Int> a@5@15))
  (<= 0 (inv@74@15 (slot<Ref> a@5@15 k@92@15))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 45 | !(pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@92@15)))]
(assert (not
  (<=
    pivot@66@15
    ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@92@15)))))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (<=
      pivot@66@15
      ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@92@15))))
  (<=
    pivot@66@15
    ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@92@15)))))
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
; [else-branch: 44 | !(k@92@15 <= hi@7@15 && i@39@15 + 1 <= k@92@15)]
(assert (not (and (<= k@92@15 hi@7@15) (<= (+ i@39@15 1) k@92@15))))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (=>
  (and (<= k@92@15 hi@7@15) (<= (+ i@39@15 1) k@92@15))
  (and
    (<= k@92@15 hi@7@15)
    (<= (+ i@39@15 1) k@92@15)
    (or
      (not
        (<=
          pivot@66@15
          ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@92@15))))
      (<=
        pivot@66@15
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@92@15)))))))
; Joined path conditions
(assert (or
  (not (and (<= k@92@15 hi@7@15) (<= (+ i@39@15 1) k@92@15)))
  (and (<= k@92@15 hi@7@15) (<= (+ i@39@15 1) k@92@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@92@15 Int)) (!
  (and
    (or (not (<= (+ i@39@15 1) k@92@15)) (<= (+ i@39@15 1) k@92@15))
    (=>
      (and (<= k@92@15 hi@7@15) (<= (+ i@39@15 1) k@92@15))
      (and
        (<= k@92@15 hi@7@15)
        (<= (+ i@39@15 1) k@92@15)
        (or
          (not
            (<=
              pivot@66@15
              ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@92@15))))
          (<=
            pivot@66@15
            ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@92@15))))))
    (or
      (not (and (<= k@92@15 hi@7@15) (<= (+ i@39@15 1) k@92@15)))
      (and (<= k@92@15 hi@7@15) (<= (+ i@39@15 1) k@92@15))))
  :pattern ((slot<Ref> a@5@15 k@92@15))
  :qid |prog.l81-aux|)))
(set-option :timeout 0)
(push) ; 4
(assert (not (forall ((k@92@15 Int)) (!
  (=>
    (and (<= k@92@15 hi@7@15) (<= (+ i@39@15 1) k@92@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@92@15))
        rb@9@15)
      (<=
        pivot@66@15
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@92@15)))))
  :pattern ((slot<Ref> a@5@15 k@92@15))
  :qid |prog.l81|))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; [eval] (forall k: Int :: { slot(a, k) } lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb)
(declare-const k@93@15 Int)
(set-option :timeout 0)
(push) ; 4
; [eval] lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lo <= k && k <= hi
; [eval] lo <= k
(push) ; 5
; [then-branch: 46 | i@39@15 + 1 <= k@93@15 | live]
; [else-branch: 46 | !(i@39@15 + 1 <= k@93@15) | live]
(push) ; 6
; [then-branch: 46 | i@39@15 + 1 <= k@93@15]
(assert (<= (+ i@39@15 1) k@93@15))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
(declare-const pm@94@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@94@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@94@15  $FPM) r))
  :qid |qp.resPrmSumDef42|)))
; Assume upper permission bound for field val
(assert (forall ((r $Ref)) (!
  (<= ($FVF.perm_val (as pm@94@15  $FPM) r) $Perm.Write)
  :pattern ((inv@74@15 r))
  :qid |qp-fld-prm-bnd|)))
; [eval] k <= hi
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
; [else-branch: 46 | !(i@39@15 + 1 <= k@93@15)]
(assert (not (<= (+ i@39@15 1) k@93@15)))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
(declare-const pm@95@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@95@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@95@15  $FPM) r))
  :qid |qp.resPrmSumDef43|)))
; Assume upper permission bound for field val
(assert (forall ((r $Ref)) (!
  (<= ($FVF.perm_val (as pm@95@15  $FPM) r) $Perm.Write)
  :pattern ((inv@74@15 r))
  :qid |qp-fld-prm-bnd|)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@94@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@94@15  $FPM) r))
  :qid |qp.resPrmSumDef42|)))
(assert (=>
  (<= (+ i@39@15 1) k@93@15)
  (and
    (<= (+ i@39@15 1) k@93@15)
    (forall ((r $Ref)) (!
      (<= ($FVF.perm_val (as pm@94@15  $FPM) r) $Perm.Write)
      :pattern ((inv@74@15 r))
      :qid |qp-fld-prm-bnd|)))))
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@95@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@95@15  $FPM) r))
  :qid |qp.resPrmSumDef43|)))
(assert (=>
  (not (<= (+ i@39@15 1) k@93@15))
  (and
    (not (<= (+ i@39@15 1) k@93@15))
    (forall ((r $Ref)) (!
      (<= ($FVF.perm_val (as pm@95@15  $FPM) r) $Perm.Write)
      :pattern ((inv@74@15 r))
      :qid |qp-fld-prm-bnd|)))))
(assert (or (not (<= (+ i@39@15 1) k@93@15)) (<= (+ i@39@15 1) k@93@15)))
(set-option :timeout 0)
(push) ; 5
; [then-branch: 47 | k@93@15 <= hi@7@15 && i@39@15 + 1 <= k@93@15 | live]
; [else-branch: 47 | !(k@93@15 <= hi@7@15 && i@39@15 + 1 <= k@93@15) | live]
(push) ; 6
; [then-branch: 47 | k@93@15 <= hi@7@15 && i@39@15 + 1 <= k@93@15]
(assert (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15)))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
(assert (forall ((r $Ref)) (!
  (<= ($FVF.perm_val (as pm@95@15  $FPM) r) $Perm.Write)
  :pattern ((inv@74@15 r))
  :qid |qp-fld-prm-bnd|)))
; [eval] lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lb <= slot(a, k).val
; [eval] slot(a, k)
(set-option :timeout 0)
(push) ; 7
(assert (not (and
  (< (inv@74@15 (slot<Ref> a@5@15 k@93@15)) (len<Int> a@5@15))
  (<= 0 (inv@74@15 (slot<Ref> a@5@15 k@93@15))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch: 48 | pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@93@15)) | live]
; [else-branch: 48 | !(pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@93@15))) | live]
(push) ; 8
; [then-branch: 48 | pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@93@15))]
(assert (<=
  pivot@66@15
  ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@93@15))))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
; [eval] slot(a, k).val <= rb
; [eval] slot(a, k)
(set-option :timeout 0)
(push) ; 9
(assert (not (and
  (< (inv@74@15 (slot<Ref> a@5@15 k@93@15)) (len<Int> a@5@15))
  (<= 0 (inv@74@15 (slot<Ref> a@5@15 k@93@15))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 48 | !(pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@93@15)))]
(assert (not
  (<=
    pivot@66@15
    ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@93@15)))))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (<=
      pivot@66@15
      ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@93@15))))
  (<=
    pivot@66@15
    ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@93@15)))))
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
; [else-branch: 47 | !(k@93@15 <= hi@7@15 && i@39@15 + 1 <= k@93@15)]
(assert (not (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15))))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
(assert (forall ((r $Ref)) (!
  (<= ($FVF.perm_val (as pm@95@15  $FPM) r) $Perm.Write)
  :pattern ((inv@74@15 r))
  :qid |qp-fld-prm-bnd|)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (=>
  (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15))
  (and
    (<= k@93@15 hi@7@15)
    (<= (+ i@39@15 1) k@93@15)
    (forall ((r $Ref)) (!
      (<= ($FVF.perm_val (as pm@95@15  $FPM) r) $Perm.Write)
      :pattern ((inv@74@15 r))
      :qid |qp-fld-prm-bnd|))
    (or
      (not
        (<=
          pivot@66@15
          ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@93@15))))
      (<=
        pivot@66@15
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@93@15)))))))
; Joined path conditions
(assert (=>
  (not (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15)))
  (and
    (not (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15)))
    (forall ((r $Ref)) (!
      (<= ($FVF.perm_val (as pm@95@15  $FPM) r) $Perm.Write)
      :pattern ((inv@74@15 r))
      :qid |qp-fld-prm-bnd|)))))
(assert (or
  (not (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15)))
  (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@94@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@94@15  $FPM) r))
  :qid |qp.resPrmSumDef42|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@95@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@95@15  $FPM) r))
  :qid |qp.resPrmSumDef43|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@93@15 Int)) (!
  (and
    (=>
      (<= (+ i@39@15 1) k@93@15)
      (and
        (<= (+ i@39@15 1) k@93@15)
        (forall ((r $Ref)) (!
          (<= ($FVF.perm_val (as pm@94@15  $FPM) r) $Perm.Write)
          :pattern ((inv@74@15 r))
          :qid |qp-fld-prm-bnd|))))
    (=>
      (not (<= (+ i@39@15 1) k@93@15))
      (and
        (not (<= (+ i@39@15 1) k@93@15))
        (forall ((r $Ref)) (!
          (<= ($FVF.perm_val (as pm@95@15  $FPM) r) $Perm.Write)
          :pattern ((inv@74@15 r))
          :qid |qp-fld-prm-bnd|))))
    (or (not (<= (+ i@39@15 1) k@93@15)) (<= (+ i@39@15 1) k@93@15))
    (=>
      (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15))
      (and
        (<= k@93@15 hi@7@15)
        (<= (+ i@39@15 1) k@93@15)
        (forall ((r $Ref)) (!
          (<= ($FVF.perm_val (as pm@95@15  $FPM) r) $Perm.Write)
          :pattern ((inv@74@15 r))
          :qid |qp-fld-prm-bnd|))
        (or
          (not
            (<=
              pivot@66@15
              ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@93@15))))
          (<=
            pivot@66@15
            ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@93@15))))))
    (=>
      (not (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15)))
      (and
        (not (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15)))
        (forall ((r $Ref)) (!
          (<= ($FVF.perm_val (as pm@95@15  $FPM) r) $Perm.Write)
          :pattern ((inv@74@15 r))
          :qid |qp-fld-prm-bnd|))))
    (or
      (not (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15)))
      (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15))))
  :pattern ((slot<Ref> a@5@15 k@93@15))
  :qid |prog.l81-aux|)))
(set-option :timeout 0)
(push) ; 4
(assert (not (forall ((k@93@15 Int)) (!
  (=>
    (and (<= k@93@15 hi@7@15) (<= (+ i@39@15 1) k@93@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@93@15))
        rb@9@15)
      (<=
        pivot@66@15
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@93@15)))))
  :pattern ((slot<Ref> a@5@15 k@93@15))
  :qid |prog.l81|))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
(declare-const pm@96@15 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@96@15  $FPM) r)
    (ite
      (and (< (inv@74@15 r) (len<Int> a@5@15)) (<= 0 (inv@74@15 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@96@15  $FPM) r))
  :qid |qp.resPrmSumDef44|)))
; Assume upper permission bound for field val
(assert (forall ((r $Ref)) (!
  (<= ($FVF.perm_val (as pm@96@15  $FPM) r) $Perm.Write)
  :pattern ((inv@74@15 r))
  :qid |qp-fld-prm-bnd|)))
; [eval] (forall k: Int :: { slot(a, k) } lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb)
(declare-const k@97@15 Int)
(set-option :timeout 0)
(push) ; 4
; [eval] lo <= k && k <= hi ==> lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lo <= k && k <= hi
; [eval] lo <= k
(push) ; 5
; [then-branch: 49 | i@39@15 + 1 <= k@97@15 | live]
; [else-branch: 49 | !(i@39@15 + 1 <= k@97@15) | live]
(push) ; 6
; [then-branch: 49 | i@39@15 + 1 <= k@97@15]
(assert (<= (+ i@39@15 1) k@97@15))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
; [eval] k <= hi
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
; [else-branch: 49 | !(i@39@15 + 1 <= k@97@15)]
(assert (not (<= (+ i@39@15 1) k@97@15)))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= (+ i@39@15 1) k@97@15)) (<= (+ i@39@15 1) k@97@15)))
(set-option :timeout 0)
(push) ; 5
; [then-branch: 50 | k@97@15 <= hi@7@15 && i@39@15 + 1 <= k@97@15 | live]
; [else-branch: 50 | !(k@97@15 <= hi@7@15 && i@39@15 + 1 <= k@97@15) | live]
(push) ; 6
; [then-branch: 50 | k@97@15 <= hi@7@15 && i@39@15 + 1 <= k@97@15]
(assert (and (<= k@97@15 hi@7@15) (<= (+ i@39@15 1) k@97@15)))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
; [eval] lb <= slot(a, k).val && slot(a, k).val <= rb
; [eval] lb <= slot(a, k).val
; [eval] slot(a, k)
(set-option :timeout 0)
(push) ; 7
(assert (not (and
  (< (inv@74@15 (slot<Ref> a@5@15 k@97@15)) (len<Int> a@5@15))
  (<= 0 (inv@74@15 (slot<Ref> a@5@15 k@97@15))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch: 51 | pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@97@15)) | live]
; [else-branch: 51 | !(pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@97@15))) | live]
(push) ; 8
; [then-branch: 51 | pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@97@15))]
(assert (<=
  pivot@66@15
  ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@97@15))))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
; [eval] slot(a, k).val <= rb
; [eval] slot(a, k)
(set-option :timeout 0)
(push) ; 9
(assert (not (and
  (< (inv@74@15 (slot<Ref> a@5@15 k@97@15)) (len<Int> a@5@15))
  (<= 0 (inv@74@15 (slot<Ref> a@5@15 k@97@15))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 51 | !(pivot@66@15 <= Lookup(val,sm@89@15,slot[Ref](a@5@15, k@97@15)))]
(assert (not
  (<=
    pivot@66@15
    ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@97@15)))))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (<=
      pivot@66@15
      ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@97@15))))
  (<=
    pivot@66@15
    ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@97@15)))))
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
; [else-branch: 50 | !(k@97@15 <= hi@7@15 && i@39@15 + 1 <= k@97@15)]
(assert (not (and (<= k@97@15 hi@7@15) (<= (+ i@39@15 1) k@97@15))))
; [state consolidation]
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Definitional axioms for snapshot map values
; Assume upper permission bound for field val
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (=>
  (and (<= k@97@15 hi@7@15) (<= (+ i@39@15 1) k@97@15))
  (and
    (<= k@97@15 hi@7@15)
    (<= (+ i@39@15 1) k@97@15)
    (or
      (not
        (<=
          pivot@66@15
          ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@97@15))))
      (<=
        pivot@66@15
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@97@15)))))))
; Joined path conditions
(assert (or
  (not (and (<= k@97@15 hi@7@15) (<= (+ i@39@15 1) k@97@15)))
  (and (<= k@97@15 hi@7@15) (<= (+ i@39@15 1) k@97@15))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@97@15 Int)) (!
  (and
    (or (not (<= (+ i@39@15 1) k@97@15)) (<= (+ i@39@15 1) k@97@15))
    (=>
      (and (<= k@97@15 hi@7@15) (<= (+ i@39@15 1) k@97@15))
      (and
        (<= k@97@15 hi@7@15)
        (<= (+ i@39@15 1) k@97@15)
        (or
          (not
            (<=
              pivot@66@15
              ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@97@15))))
          (<=
            pivot@66@15
            ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@97@15))))))
    (or
      (not (and (<= k@97@15 hi@7@15) (<= (+ i@39@15 1) k@97@15)))
      (and (<= k@97@15 hi@7@15) (<= (+ i@39@15 1) k@97@15))))
  :pattern ((slot<Ref> a@5@15 k@97@15))
  :qid |prog.l81-aux|)))
(set-option :timeout 0)
(push) ; 4
(assert (not (forall ((k@97@15 Int)) (!
  (=>
    (and (<= k@97@15 hi@7@15) (<= (+ i@39@15 1) k@97@15))
    (and
      (<=
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@97@15))
        rb@9@15)
      (<=
        pivot@66@15
        ($FVF.lookup_val (as sm@89@15  $FVF<val>) (slot<Ref> a@5@15 k@97@15)))))
  :pattern ((slot<Ref> a@5@15 k@97@15))
  :qid |prog.l81|))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(pop) ; 3
(pop) ; 2
(pop) ; 1
