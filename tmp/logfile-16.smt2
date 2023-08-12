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
; ---------- partition ----------
(declare-const a@0@16 IArray)
(declare-const lo@1@16 Int)
(declare-const hi@2@16 Int)
(declare-const lb@3@16 Int)
(declare-const rb@4@16 Int)
(declare-const i@5@16 Int)
(declare-const a@6@16 IArray)
(declare-const lo@7@16 Int)
(declare-const hi@8@16 Int)
(declare-const lb@9@16 Int)
(declare-const rb@10@16 Int)
(declare-const i@11@16 Int)
(set-option :timeout 0)
(push) ; 1
(declare-const $t@12@16 $Snap)
(assert (= $t@12@16 ($Snap.combine ($Snap.first $t@12@16) ($Snap.second $t@12@16))))
(declare-const j$0@13@16 Int)
(push) ; 2
; [eval] 0 <= j$0 && j$0 < len(a)
; [eval] 0 <= j$0
(push) ; 3
; [then-branch: 0 | 0 <= j$0@13@16 | live]
; [else-branch: 0 | !(0 <= j$0@13@16) | live]
(push) ; 4
; [then-branch: 0 | 0 <= j$0@13@16]
(assert (<= 0 j$0@13@16))
; [eval] j$0 < len(a)
; [eval] len(a)
(pop) ; 4
(push) ; 4
; [else-branch: 0 | !(0 <= j$0@13@16)]
(assert (not (<= 0 j$0@13@16)))
(pop) ; 4
(pop) ; 3
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$0@13@16)) (<= 0 j$0@13@16)))
(assert (and (< j$0@13@16 (len<Int> a@6@16)) (<= 0 j$0@13@16)))
; [eval] slot(a, j$0)
(pop) ; 2
(declare-fun inv@14@16 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$0@13@16 Int)) (!
  (=>
    (and (< j$0@13@16 (len<Int> a@6@16)) (<= 0 j$0@13@16))
    (or (not (<= 0 j$0@13@16)) (<= 0 j$0@13@16)))
  :pattern ((slot<Ref> a@6@16 j$0@13@16))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 2
(assert (not (forall ((j$01@13@16 Int) (j$02@13@16 Int)) (!
  (=>
    (and
      (and (< j$01@13@16 (len<Int> a@6@16)) (<= 0 j$01@13@16))
      (and (< j$02@13@16 (len<Int> a@6@16)) (<= 0 j$02@13@16))
      (= (slot<Ref> a@6@16 j$01@13@16) (slot<Ref> a@6@16 j$02@13@16)))
    (= j$01@13@16 j$02@13@16))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 2
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$0@13@16 Int)) (!
  (=>
    (and (< j$0@13@16 (len<Int> a@6@16)) (<= 0 j$0@13@16))
    (= (inv@14@16 (slot<Ref> a@6@16 j$0@13@16)) j$0@13@16))
  :pattern ((slot<Ref> a@6@16 j$0@13@16))
  :qid |quant-u-3|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (= (slot<Ref> a@6@16 (inv@14@16 r)) r))
  :pattern ((inv@14@16 r))
  :qid |val-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j$0@13@16 Int)) (!
  (=>
    (and (< j$0@13@16 (len<Int> a@6@16)) (<= 0 j$0@13@16))
    (not (= (slot<Ref> a@6@16 j$0@13@16) $Ref.null)))
  :pattern ((slot<Ref> a@6@16 j$0@13@16))
  :qid |val-permImpliesNonNull|)))
(assert (=
  ($Snap.second $t@12@16)
  ($Snap.combine
    ($Snap.first ($Snap.second $t@12@16))
    ($Snap.second ($Snap.second $t@12@16)))))
(assert (= ($Snap.first ($Snap.second $t@12@16)) $Snap.unit))
; [eval] hi >= 0
(assert (>= hi@8@16 0))
(assert (=
  ($Snap.second ($Snap.second $t@12@16))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second $t@12@16)))
    ($Snap.second ($Snap.second ($Snap.second $t@12@16))))))
(assert (= ($Snap.first ($Snap.second ($Snap.second $t@12@16))) $Snap.unit))
; [eval] hi < len(a)
; [eval] len(a)
(assert (< hi@8@16 (len<Int> a@6@16)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second $t@12@16)))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@12@16))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@12@16)))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@12@16))))
  $Snap.unit))
; [eval] lo >= 0
(assert (>= lo@7@16 0))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@12@16))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@12@16)))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@12@16))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@12@16)))))
  $Snap.unit))
; [eval] lo <= hi
(assert (<= lo@7@16 hi@8@16))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@12@16)))))
  $Snap.unit))
; [eval] (forall k$0: Int :: { slot(a, k$0) } lo <= k$0 && k$0 <= hi ==> lb <= slot(a, k$0).val && slot(a, k$0).val <= rb)
(declare-const k$0@15@16 Int)
(push) ; 2
; [eval] lo <= k$0 && k$0 <= hi ==> lb <= slot(a, k$0).val && slot(a, k$0).val <= rb
; [eval] lo <= k$0 && k$0 <= hi
; [eval] lo <= k$0
(push) ; 3
; [then-branch: 1 | lo@7@16 <= k$0@15@16 | live]
; [else-branch: 1 | !(lo@7@16 <= k$0@15@16) | live]
(push) ; 4
; [then-branch: 1 | lo@7@16 <= k$0@15@16]
(assert (<= lo@7@16 k$0@15@16))
; [eval] k$0 <= hi
(pop) ; 4
(push) ; 4
; [else-branch: 1 | !(lo@7@16 <= k$0@15@16)]
(assert (not (<= lo@7@16 k$0@15@16)))
(pop) ; 4
(pop) ; 3
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@7@16 k$0@15@16)) (<= lo@7@16 k$0@15@16)))
(push) ; 3
; [then-branch: 2 | k$0@15@16 <= hi@8@16 && lo@7@16 <= k$0@15@16 | live]
; [else-branch: 2 | !(k$0@15@16 <= hi@8@16 && lo@7@16 <= k$0@15@16) | live]
(push) ; 4
; [then-branch: 2 | k$0@15@16 <= hi@8@16 && lo@7@16 <= k$0@15@16]
(assert (and (<= k$0@15@16 hi@8@16) (<= lo@7@16 k$0@15@16)))
; [eval] lb <= slot(a, k$0).val && slot(a, k$0).val <= rb
; [eval] lb <= slot(a, k$0).val
; [eval] slot(a, k$0)
(declare-const sm@16@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@16@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@16@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef0|)))
(declare-const pm@17@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@17@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@17@16  $FPM) r))
  :qid |qp.resPrmSumDef1|)))
(push) ; 5
(assert (not (< $Perm.No ($FVF.perm_val (as pm@17@16  $FPM) (slot<Ref> a@6@16 k$0@15@16)))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch: 3 | lb@9@16 <= Lookup(val,sm@16@16,slot[Ref](a@6@16, k$0@15@16)) | live]
; [else-branch: 3 | !(lb@9@16 <= Lookup(val,sm@16@16,slot[Ref](a@6@16, k$0@15@16))) | live]
(push) ; 6
; [then-branch: 3 | lb@9@16 <= Lookup(val,sm@16@16,slot[Ref](a@6@16, k$0@15@16))]
(assert (<=
  lb@9@16
  ($FVF.lookup_val (as sm@16@16  $FVF<val>) (slot<Ref> a@6@16 k$0@15@16))))
; [eval] slot(a, k$0).val <= rb
; [eval] slot(a, k$0)
(declare-const sm@18@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@18@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@18@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef2|)))
(declare-const pm@19@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@19@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@19@16  $FPM) r))
  :qid |qp.resPrmSumDef3|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@19@16  $FPM) (slot<Ref> a@6@16 k$0@15@16)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 3 | !(lb@9@16 <= Lookup(val,sm@16@16,slot[Ref](a@6@16, k$0@15@16)))]
(assert (not
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@16@16  $FVF<val>) (slot<Ref> a@6@16 k$0@15@16)))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@18@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@18@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef2|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@19@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@19@16  $FPM) r))
  :qid |qp.resPrmSumDef3|)))
; Joined path conditions
(assert (or
  (not
    (<=
      lb@9@16
      ($FVF.lookup_val (as sm@16@16  $FVF<val>) (slot<Ref> a@6@16 k$0@15@16))))
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@16@16  $FVF<val>) (slot<Ref> a@6@16 k$0@15@16)))))
(pop) ; 4
(push) ; 4
; [else-branch: 2 | !(k$0@15@16 <= hi@8@16 && lo@7@16 <= k$0@15@16)]
(assert (not (and (<= k$0@15@16 hi@8@16) (<= lo@7@16 k$0@15@16))))
(pop) ; 4
(pop) ; 3
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@16@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@16@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef0|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@17@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@17@16  $FPM) r))
  :qid |qp.resPrmSumDef1|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@18@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@18@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef2|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@19@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@19@16  $FPM) r))
  :qid |qp.resPrmSumDef3|)))
(assert (=>
  (and (<= k$0@15@16 hi@8@16) (<= lo@7@16 k$0@15@16))
  (and
    (<= k$0@15@16 hi@8@16)
    (<= lo@7@16 k$0@15@16)
    (or
      (not
        (<=
          lb@9@16
          ($FVF.lookup_val (as sm@16@16  $FVF<val>) (slot<Ref> a@6@16 k$0@15@16))))
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@16@16  $FVF<val>) (slot<Ref> a@6@16 k$0@15@16)))))))
; Joined path conditions
(assert (or
  (not (and (<= k$0@15@16 hi@8@16) (<= lo@7@16 k$0@15@16)))
  (and (<= k$0@15@16 hi@8@16) (<= lo@7@16 k$0@15@16))))
(pop) ; 2
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@16@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@16@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef0|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@17@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@17@16  $FPM) r))
  :qid |qp.resPrmSumDef1|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@18@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@18@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef2|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@19@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@19@16  $FPM) r))
  :qid |qp.resPrmSumDef3|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$0@15@16 Int)) (!
  (and
    (or (not (<= lo@7@16 k$0@15@16)) (<= lo@7@16 k$0@15@16))
    (=>
      (and (<= k$0@15@16 hi@8@16) (<= lo@7@16 k$0@15@16))
      (and
        (<= k$0@15@16 hi@8@16)
        (<= lo@7@16 k$0@15@16)
        (or
          (not
            (<=
              lb@9@16
              ($FVF.lookup_val (as sm@16@16  $FVF<val>) (slot<Ref> a@6@16 k$0@15@16))))
          (<=
            lb@9@16
            ($FVF.lookup_val (as sm@16@16  $FVF<val>) (slot<Ref> a@6@16 k$0@15@16))))))
    (or
      (not (and (<= k$0@15@16 hi@8@16) (<= lo@7@16 k$0@15@16)))
      (and (<= k$0@15@16 hi@8@16) (<= lo@7@16 k$0@15@16))))
  :pattern ((slot<Ref> a@6@16 k$0@15@16))
  :qid |prog.l36-aux|)))
(assert (forall ((k$0@15@16 Int)) (!
  (=>
    (and (<= k$0@15@16 hi@8@16) (<= lo@7@16 k$0@15@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@18@16  $FVF<val>) (slot<Ref> a@6@16 k$0@15@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@16@16  $FVF<val>) (slot<Ref> a@6@16 k$0@15@16)))))
  :pattern ((slot<Ref> a@6@16 k$0@15@16))
  :qid |prog.l36|)))
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
(set-option :timeout 0)
(push) ; 2
(declare-const $t@20@16 $Snap)
(assert (= $t@20@16 ($Snap.combine ($Snap.first $t@20@16) ($Snap.second $t@20@16))))
(declare-const j$1@21@16 Int)
(push) ; 3
; [eval] 0 <= j$1 && j$1 < len(a)
; [eval] 0 <= j$1
(push) ; 4
; [then-branch: 4 | 0 <= j$1@21@16 | live]
; [else-branch: 4 | !(0 <= j$1@21@16) | live]
(push) ; 5
; [then-branch: 4 | 0 <= j$1@21@16]
(assert (<= 0 j$1@21@16))
; [eval] j$1 < len(a)
; [eval] len(a)
(pop) ; 5
(push) ; 5
; [else-branch: 4 | !(0 <= j$1@21@16)]
(assert (not (<= 0 j$1@21@16)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$1@21@16)) (<= 0 j$1@21@16)))
(assert (and (< j$1@21@16 (len<Int> a@6@16)) (<= 0 j$1@21@16)))
; [eval] slot(a, j$1)
(pop) ; 3
(declare-fun inv@22@16 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$1@21@16 Int)) (!
  (=>
    (and (< j$1@21@16 (len<Int> a@6@16)) (<= 0 j$1@21@16))
    (or (not (<= 0 j$1@21@16)) (<= 0 j$1@21@16)))
  :pattern ((slot<Ref> a@6@16 j$1@21@16))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 3
(assert (not (forall ((j$11@21@16 Int) (j$12@21@16 Int)) (!
  (=>
    (and
      (and (< j$11@21@16 (len<Int> a@6@16)) (<= 0 j$11@21@16))
      (and (< j$12@21@16 (len<Int> a@6@16)) (<= 0 j$12@21@16))
      (= (slot<Ref> a@6@16 j$11@21@16) (slot<Ref> a@6@16 j$12@21@16)))
    (= j$11@21@16 j$12@21@16))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$1@21@16 Int)) (!
  (=>
    (and (< j$1@21@16 (len<Int> a@6@16)) (<= 0 j$1@21@16))
    (= (inv@22@16 (slot<Ref> a@6@16 j$1@21@16)) j$1@21@16))
  :pattern ((slot<Ref> a@6@16 j$1@21@16))
  :qid |quant-u-7|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (= (slot<Ref> a@6@16 (inv@22@16 r)) r))
  :pattern ((inv@22@16 r))
  :qid |val-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j$1@21@16 Int)) (!
  (=>
    (and (< j$1@21@16 (len<Int> a@6@16)) (<= 0 j$1@21@16))
    (not (= (slot<Ref> a@6@16 j$1@21@16) $Ref.null)))
  :pattern ((slot<Ref> a@6@16 j$1@21@16))
  :qid |val-permImpliesNonNull|)))
(assert (=
  ($Snap.second $t@20@16)
  ($Snap.combine
    ($Snap.first ($Snap.second $t@20@16))
    ($Snap.second ($Snap.second $t@20@16)))))
(assert (= ($Snap.first ($Snap.second $t@20@16)) $Snap.unit))
; [eval] i >= lo
(assert (>= i@11@16 lo@7@16))
(assert (=
  ($Snap.second ($Snap.second $t@20@16))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second $t@20@16)))
    ($Snap.second ($Snap.second ($Snap.second $t@20@16))))))
(assert (= ($Snap.first ($Snap.second ($Snap.second $t@20@16))) $Snap.unit))
; [eval] i <= hi
(assert (<= i@11@16 hi@8@16))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second $t@20@16)))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@20@16))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16)))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@20@16))))
  $Snap.unit))
; [eval] (forall k: Int :: { slot(a, k) } k >= lo && k <= i ==> slot(a, k).val <= slot(a, i).val)
(declare-const k@23@16 Int)
(push) ; 3
; [eval] k >= lo && k <= i ==> slot(a, k).val <= slot(a, i).val
; [eval] k >= lo && k <= i
; [eval] k >= lo
(push) ; 4
; [then-branch: 5 | k@23@16 >= lo@7@16 | live]
; [else-branch: 5 | !(k@23@16 >= lo@7@16) | live]
(push) ; 5
; [then-branch: 5 | k@23@16 >= lo@7@16]
(assert (>= k@23@16 lo@7@16))
; [eval] k <= i
(pop) ; 5
(push) ; 5
; [else-branch: 5 | !(k@23@16 >= lo@7@16)]
(assert (not (>= k@23@16 lo@7@16)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@23@16 lo@7@16)) (>= k@23@16 lo@7@16)))
(push) ; 4
; [then-branch: 6 | k@23@16 <= i@11@16 && k@23@16 >= lo@7@16 | live]
; [else-branch: 6 | !(k@23@16 <= i@11@16 && k@23@16 >= lo@7@16) | live]
(push) ; 5
; [then-branch: 6 | k@23@16 <= i@11@16 && k@23@16 >= lo@7@16]
(assert (and (<= k@23@16 i@11@16) (>= k@23@16 lo@7@16)))
; [eval] slot(a, k).val <= slot(a, i).val
; [eval] slot(a, k)
(declare-const sm@24@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@24@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@24@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef4|)))
(declare-const pm@25@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@25@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@25@16  $FPM) r))
  :qid |qp.resPrmSumDef5|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@25@16  $FPM) (slot<Ref> a@6@16 k@23@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] slot(a, i)
(declare-const sm@26@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@26@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@26@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef6|)))
(declare-const pm@27@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@27@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@27@16  $FPM) r))
  :qid |qp.resPrmSumDef7|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@27@16  $FPM) (slot<Ref> a@6@16 i@11@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(pop) ; 5
(push) ; 5
; [else-branch: 6 | !(k@23@16 <= i@11@16 && k@23@16 >= lo@7@16)]
(assert (not (and (<= k@23@16 i@11@16) (>= k@23@16 lo@7@16))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@24@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@24@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef4|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@25@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@25@16  $FPM) r))
  :qid |qp.resPrmSumDef5|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@26@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@26@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef6|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@27@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@27@16  $FPM) r))
  :qid |qp.resPrmSumDef7|)))
; Joined path conditions
(assert (or
  (not (and (<= k@23@16 i@11@16) (>= k@23@16 lo@7@16)))
  (and (<= k@23@16 i@11@16) (>= k@23@16 lo@7@16))))
(pop) ; 3
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@24@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@24@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef4|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@25@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@25@16  $FPM) r))
  :qid |qp.resPrmSumDef5|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@26@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@26@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef6|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@27@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@27@16  $FPM) r))
  :qid |qp.resPrmSumDef7|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@23@16 Int)) (!
  (and
    (or (not (>= k@23@16 lo@7@16)) (>= k@23@16 lo@7@16))
    (or
      (not (and (<= k@23@16 i@11@16) (>= k@23@16 lo@7@16)))
      (and (<= k@23@16 i@11@16) (>= k@23@16 lo@7@16))))
  :pattern ((slot<Ref> a@6@16 k@23@16))
  :qid |prog.l39-aux|)))
(assert (forall ((k@23@16 Int)) (!
  (=>
    (and (<= k@23@16 i@11@16) (>= k@23@16 lo@7@16))
    (<=
      ($FVF.lookup_val (as sm@24@16  $FVF<val>) (slot<Ref> a@6@16 k@23@16))
      ($FVF.lookup_val (as sm@26@16  $FVF<val>) (slot<Ref> a@6@16 i@11@16))))
  :pattern ((slot<Ref> a@6@16 k@23@16))
  :qid |prog.l39|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16)))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16)))))
  $Snap.unit))
; [eval] (forall k: Int :: { slot(a, k) } k >= i + 1 && k <= hi ==> slot(a, k).val > slot(a, i).val)
(declare-const k@28@16 Int)
(push) ; 3
; [eval] k >= i + 1 && k <= hi ==> slot(a, k).val > slot(a, i).val
; [eval] k >= i + 1 && k <= hi
; [eval] k >= i + 1
; [eval] i + 1
(push) ; 4
; [then-branch: 7 | k@28@16 >= i@11@16 + 1 | live]
; [else-branch: 7 | !(k@28@16 >= i@11@16 + 1) | live]
(push) ; 5
; [then-branch: 7 | k@28@16 >= i@11@16 + 1]
(assert (>= k@28@16 (+ i@11@16 1)))
; [eval] k <= hi
(pop) ; 5
(push) ; 5
; [else-branch: 7 | !(k@28@16 >= i@11@16 + 1)]
(assert (not (>= k@28@16 (+ i@11@16 1))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@28@16 (+ i@11@16 1))) (>= k@28@16 (+ i@11@16 1))))
(push) ; 4
; [then-branch: 8 | k@28@16 <= hi@8@16 && k@28@16 >= i@11@16 + 1 | live]
; [else-branch: 8 | !(k@28@16 <= hi@8@16 && k@28@16 >= i@11@16 + 1) | live]
(push) ; 5
; [then-branch: 8 | k@28@16 <= hi@8@16 && k@28@16 >= i@11@16 + 1]
(assert (and (<= k@28@16 hi@8@16) (>= k@28@16 (+ i@11@16 1))))
; [eval] slot(a, k).val > slot(a, i).val
; [eval] slot(a, k)
(declare-const sm@29@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@29@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@29@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef8|)))
(declare-const pm@30@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@30@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@30@16  $FPM) r))
  :qid |qp.resPrmSumDef9|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@30@16  $FPM) (slot<Ref> a@6@16 k@28@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] slot(a, i)
(declare-const sm@31@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@31@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@31@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef10|)))
(declare-const pm@32@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@32@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@32@16  $FPM) r))
  :qid |qp.resPrmSumDef11|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@32@16  $FPM) (slot<Ref> a@6@16 i@11@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(pop) ; 5
(push) ; 5
; [else-branch: 8 | !(k@28@16 <= hi@8@16 && k@28@16 >= i@11@16 + 1)]
(assert (not (and (<= k@28@16 hi@8@16) (>= k@28@16 (+ i@11@16 1)))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@29@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@29@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef8|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@30@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@30@16  $FPM) r))
  :qid |qp.resPrmSumDef9|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@31@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@31@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef10|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@32@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@32@16  $FPM) r))
  :qid |qp.resPrmSumDef11|)))
; Joined path conditions
(assert (or
  (not (and (<= k@28@16 hi@8@16) (>= k@28@16 (+ i@11@16 1))))
  (and (<= k@28@16 hi@8@16) (>= k@28@16 (+ i@11@16 1)))))
(pop) ; 3
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@29@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@29@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef8|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@30@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@30@16  $FPM) r))
  :qid |qp.resPrmSumDef9|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@31@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@31@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef10|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@32@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@32@16  $FPM) r))
  :qid |qp.resPrmSumDef11|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@28@16 Int)) (!
  (and
    (or (not (>= k@28@16 (+ i@11@16 1))) (>= k@28@16 (+ i@11@16 1)))
    (or
      (not (and (<= k@28@16 hi@8@16) (>= k@28@16 (+ i@11@16 1))))
      (and (<= k@28@16 hi@8@16) (>= k@28@16 (+ i@11@16 1)))))
  :pattern ((slot<Ref> a@6@16 k@28@16))
  :qid |prog.l40-aux|)))
(assert (forall ((k@28@16 Int)) (!
  (=>
    (and (<= k@28@16 hi@8@16) (>= k@28@16 (+ i@11@16 1)))
    (>
      ($FVF.lookup_val (as sm@29@16  $FVF<val>) (slot<Ref> a@6@16 k@28@16))
      ($FVF.lookup_val (as sm@31@16  $FVF<val>) (slot<Ref> a@6@16 i@11@16))))
  :pattern ((slot<Ref> a@6@16 k@28@16))
  :qid |prog.l40|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16)))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16)))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16))))))
  $Snap.unit))
; [eval] (forall k$1: Int :: { slot(a, k$1) } 0 <= k$1 && k$1 <= lo - 1 ==> slot(a, k$1).val == old(slot(a, k$1).val))
(declare-const k$1@33@16 Int)
(push) ; 3
; [eval] 0 <= k$1 && k$1 <= lo - 1 ==> slot(a, k$1).val == old(slot(a, k$1).val)
; [eval] 0 <= k$1 && k$1 <= lo - 1
; [eval] 0 <= k$1
(push) ; 4
; [then-branch: 9 | 0 <= k$1@33@16 | live]
; [else-branch: 9 | !(0 <= k$1@33@16) | live]
(push) ; 5
; [then-branch: 9 | 0 <= k$1@33@16]
(assert (<= 0 k$1@33@16))
; [eval] k$1 <= lo - 1
; [eval] lo - 1
(pop) ; 5
(push) ; 5
; [else-branch: 9 | !(0 <= k$1@33@16)]
(assert (not (<= 0 k$1@33@16)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 k$1@33@16)) (<= 0 k$1@33@16)))
(push) ; 4
; [then-branch: 10 | k$1@33@16 <= lo@7@16 - 1 && 0 <= k$1@33@16 | live]
; [else-branch: 10 | !(k$1@33@16 <= lo@7@16 - 1 && 0 <= k$1@33@16) | live]
(push) ; 5
; [then-branch: 10 | k$1@33@16 <= lo@7@16 - 1 && 0 <= k$1@33@16]
(assert (and (<= k$1@33@16 (- lo@7@16 1)) (<= 0 k$1@33@16)))
; [eval] slot(a, k$1).val == old(slot(a, k$1).val)
; [eval] slot(a, k$1)
(declare-const sm@34@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@34@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@34@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef12|)))
(declare-const pm@35@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@35@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@35@16  $FPM) r))
  :qid |qp.resPrmSumDef13|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@35@16  $FPM) (slot<Ref> a@6@16 k$1@33@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$1).val)
; [eval] slot(a, k$1)
(declare-const sm@36@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@36@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@36@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef14|)))
(declare-const pm@37@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@37@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@37@16  $FPM) r))
  :qid |qp.resPrmSumDef15|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@37@16  $FPM) (slot<Ref> a@6@16 k$1@33@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(pop) ; 5
(push) ; 5
; [else-branch: 10 | !(k$1@33@16 <= lo@7@16 - 1 && 0 <= k$1@33@16)]
(assert (not (and (<= k$1@33@16 (- lo@7@16 1)) (<= 0 k$1@33@16))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@34@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@34@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef12|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@35@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@35@16  $FPM) r))
  :qid |qp.resPrmSumDef13|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@36@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@36@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef14|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@37@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@37@16  $FPM) r))
  :qid |qp.resPrmSumDef15|)))
; Joined path conditions
(assert (or
  (not (and (<= k$1@33@16 (- lo@7@16 1)) (<= 0 k$1@33@16)))
  (and (<= k$1@33@16 (- lo@7@16 1)) (<= 0 k$1@33@16))))
(pop) ; 3
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@34@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@34@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef12|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@35@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@35@16  $FPM) r))
  :qid |qp.resPrmSumDef13|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@36@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@36@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef14|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@37@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@37@16  $FPM) r))
  :qid |qp.resPrmSumDef15|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$1@33@16 Int)) (!
  (and
    (or (not (<= 0 k$1@33@16)) (<= 0 k$1@33@16))
    (or
      (not (and (<= k$1@33@16 (- lo@7@16 1)) (<= 0 k$1@33@16)))
      (and (<= k$1@33@16 (- lo@7@16 1)) (<= 0 k$1@33@16))))
  :pattern ((slot<Ref> a@6@16 k$1@33@16))
  :qid |prog.l41-aux|)))
(assert (forall ((k$1@33@16 Int)) (!
  (=>
    (and (<= k$1@33@16 (- lo@7@16 1)) (<= 0 k$1@33@16))
    (=
      ($FVF.lookup_val (as sm@34@16  $FVF<val>) (slot<Ref> a@6@16 k$1@33@16))
      ($FVF.lookup_val (as sm@36@16  $FVF<val>) (slot<Ref> a@6@16 k$1@33@16))))
  :pattern ((slot<Ref> a@6@16 k$1@33@16))
  :qid |prog.l41|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16)))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16)))))))
  $Snap.unit))
; [eval] (forall k$2: Int :: { slot(a, k$2) } hi + 1 <= k$2 && k$2 <= len(a) - 1 ==> slot(a, k$2).val == old(slot(a, k$2).val))
(declare-const k$2@38@16 Int)
(push) ; 3
; [eval] hi + 1 <= k$2 && k$2 <= len(a) - 1 ==> slot(a, k$2).val == old(slot(a, k$2).val)
; [eval] hi + 1 <= k$2 && k$2 <= len(a) - 1
; [eval] hi + 1 <= k$2
; [eval] hi + 1
(push) ; 4
; [then-branch: 11 | hi@8@16 + 1 <= k$2@38@16 | live]
; [else-branch: 11 | !(hi@8@16 + 1 <= k$2@38@16) | live]
(push) ; 5
; [then-branch: 11 | hi@8@16 + 1 <= k$2@38@16]
(assert (<= (+ hi@8@16 1) k$2@38@16))
; [eval] k$2 <= len(a) - 1
; [eval] len(a) - 1
; [eval] len(a)
(pop) ; 5
(push) ; 5
; [else-branch: 11 | !(hi@8@16 + 1 <= k$2@38@16)]
(assert (not (<= (+ hi@8@16 1) k$2@38@16)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (not (<= (+ hi@8@16 1) k$2@38@16)) (<= (+ hi@8@16 1) k$2@38@16)))
(push) ; 4
; [then-branch: 12 | k$2@38@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$2@38@16 | live]
; [else-branch: 12 | !(k$2@38@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$2@38@16) | live]
(push) ; 5
; [then-branch: 12 | k$2@38@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$2@38@16]
(assert (and (<= k$2@38@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@38@16)))
; [eval] slot(a, k$2).val == old(slot(a, k$2).val)
; [eval] slot(a, k$2)
(declare-const sm@39@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@39@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@39@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef16|)))
(declare-const pm@40@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@40@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@40@16  $FPM) r))
  :qid |qp.resPrmSumDef17|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@40@16  $FPM) (slot<Ref> a@6@16 k$2@38@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$2).val)
; [eval] slot(a, k$2)
(declare-const sm@41@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@41@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@41@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef18|)))
(declare-const pm@42@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@42@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@42@16  $FPM) r))
  :qid |qp.resPrmSumDef19|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@42@16  $FPM) (slot<Ref> a@6@16 k$2@38@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(pop) ; 5
(push) ; 5
; [else-branch: 12 | !(k$2@38@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$2@38@16)]
(assert (not (and (<= k$2@38@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@38@16))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@39@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@39@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef16|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@40@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@40@16  $FPM) r))
  :qid |qp.resPrmSumDef17|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@41@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@41@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef18|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@42@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@42@16  $FPM) r))
  :qid |qp.resPrmSumDef19|)))
; Joined path conditions
(assert (or
  (not (and (<= k$2@38@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@38@16)))
  (and (<= k$2@38@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@38@16))))
(pop) ; 3
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@39@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@39@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef16|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@40@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@40@16  $FPM) r))
  :qid |qp.resPrmSumDef17|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@41@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@41@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef18|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@42@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@42@16  $FPM) r))
  :qid |qp.resPrmSumDef19|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$2@38@16 Int)) (!
  (and
    (or (not (<= (+ hi@8@16 1) k$2@38@16)) (<= (+ hi@8@16 1) k$2@38@16))
    (or
      (not
        (and (<= k$2@38@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@38@16)))
      (and (<= k$2@38@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@38@16))))
  :pattern ((slot<Ref> a@6@16 k$2@38@16))
  :qid |prog.l42-aux|)))
(assert (forall ((k$2@38@16 Int)) (!
  (=>
    (and (<= k$2@38@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@38@16))
    (=
      ($FVF.lookup_val (as sm@39@16  $FVF<val>) (slot<Ref> a@6@16 k$2@38@16))
      ($FVF.lookup_val (as sm@41@16  $FVF<val>) (slot<Ref> a@6@16 k$2@38@16))))
  :pattern ((slot<Ref> a@6@16 k$2@38@16))
  :qid |prog.l42|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@20@16)))))))
  $Snap.unit))
; [eval] (forall k$3: Int :: { slot(a, k$3) } lo <= k$3 && k$3 <= hi ==> lb <= slot(a, k$3).val && slot(a, k$3).val <= rb)
(declare-const k$3@43@16 Int)
(push) ; 3
; [eval] lo <= k$3 && k$3 <= hi ==> lb <= slot(a, k$3).val && slot(a, k$3).val <= rb
; [eval] lo <= k$3 && k$3 <= hi
; [eval] lo <= k$3
(push) ; 4
; [then-branch: 13 | lo@7@16 <= k$3@43@16 | live]
; [else-branch: 13 | !(lo@7@16 <= k$3@43@16) | live]
(push) ; 5
; [then-branch: 13 | lo@7@16 <= k$3@43@16]
(assert (<= lo@7@16 k$3@43@16))
; [eval] k$3 <= hi
(pop) ; 5
(push) ; 5
; [else-branch: 13 | !(lo@7@16 <= k$3@43@16)]
(assert (not (<= lo@7@16 k$3@43@16)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@7@16 k$3@43@16)) (<= lo@7@16 k$3@43@16)))
(push) ; 4
; [then-branch: 14 | k$3@43@16 <= hi@8@16 && lo@7@16 <= k$3@43@16 | live]
; [else-branch: 14 | !(k$3@43@16 <= hi@8@16 && lo@7@16 <= k$3@43@16) | live]
(push) ; 5
; [then-branch: 14 | k$3@43@16 <= hi@8@16 && lo@7@16 <= k$3@43@16]
(assert (and (<= k$3@43@16 hi@8@16) (<= lo@7@16 k$3@43@16)))
; [eval] lb <= slot(a, k$3).val && slot(a, k$3).val <= rb
; [eval] lb <= slot(a, k$3).val
; [eval] slot(a, k$3)
(declare-const sm@44@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@44@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@44@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef20|)))
(declare-const pm@45@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@45@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@45@16  $FPM) r))
  :qid |qp.resPrmSumDef21|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@45@16  $FPM) (slot<Ref> a@6@16 k$3@43@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch: 15 | lb@9@16 <= Lookup(val,sm@44@16,slot[Ref](a@6@16, k$3@43@16)) | live]
; [else-branch: 15 | !(lb@9@16 <= Lookup(val,sm@44@16,slot[Ref](a@6@16, k$3@43@16))) | live]
(push) ; 7
; [then-branch: 15 | lb@9@16 <= Lookup(val,sm@44@16,slot[Ref](a@6@16, k$3@43@16))]
(assert (<=
  lb@9@16
  ($FVF.lookup_val (as sm@44@16  $FVF<val>) (slot<Ref> a@6@16 k$3@43@16))))
; [eval] slot(a, k$3).val <= rb
; [eval] slot(a, k$3)
(declare-const sm@46@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@46@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@46@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef22|)))
(declare-const pm@47@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@47@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@47@16  $FPM) r))
  :qid |qp.resPrmSumDef23|)))
(push) ; 8
(assert (not (< $Perm.No ($FVF.perm_val (as pm@47@16  $FPM) (slot<Ref> a@6@16 k$3@43@16)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(pop) ; 7
(push) ; 7
; [else-branch: 15 | !(lb@9@16 <= Lookup(val,sm@44@16,slot[Ref](a@6@16, k$3@43@16)))]
(assert (not
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@44@16  $FVF<val>) (slot<Ref> a@6@16 k$3@43@16)))))
(pop) ; 7
(pop) ; 6
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@46@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@46@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef22|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@47@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@47@16  $FPM) r))
  :qid |qp.resPrmSumDef23|)))
; Joined path conditions
(assert (or
  (not
    (<=
      lb@9@16
      ($FVF.lookup_val (as sm@44@16  $FVF<val>) (slot<Ref> a@6@16 k$3@43@16))))
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@44@16  $FVF<val>) (slot<Ref> a@6@16 k$3@43@16)))))
(pop) ; 5
(push) ; 5
; [else-branch: 14 | !(k$3@43@16 <= hi@8@16 && lo@7@16 <= k$3@43@16)]
(assert (not (and (<= k$3@43@16 hi@8@16) (<= lo@7@16 k$3@43@16))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@44@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@44@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef20|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@45@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@45@16  $FPM) r))
  :qid |qp.resPrmSumDef21|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@46@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@46@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef22|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@47@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@47@16  $FPM) r))
  :qid |qp.resPrmSumDef23|)))
(assert (=>
  (and (<= k$3@43@16 hi@8@16) (<= lo@7@16 k$3@43@16))
  (and
    (<= k$3@43@16 hi@8@16)
    (<= lo@7@16 k$3@43@16)
    (or
      (not
        (<=
          lb@9@16
          ($FVF.lookup_val (as sm@44@16  $FVF<val>) (slot<Ref> a@6@16 k$3@43@16))))
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@44@16  $FVF<val>) (slot<Ref> a@6@16 k$3@43@16)))))))
; Joined path conditions
(assert (or
  (not (and (<= k$3@43@16 hi@8@16) (<= lo@7@16 k$3@43@16)))
  (and (<= k$3@43@16 hi@8@16) (<= lo@7@16 k$3@43@16))))
(pop) ; 3
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@44@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@44@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef20|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@45@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@45@16  $FPM) r))
  :qid |qp.resPrmSumDef21|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
    (=
      ($FVF.lookup_val (as sm@46@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r)))
  :pattern (($FVF.lookup_val (as sm@46@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@20@16)) r))
  :qid |qp.fvfValDef22|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@47@16  $FPM) r)
    (ite
      (and (< (inv@22@16 r) (len<Int> a@6@16)) (<= 0 (inv@22@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@47@16  $FPM) r))
  :qid |qp.resPrmSumDef23|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$3@43@16 Int)) (!
  (and
    (or (not (<= lo@7@16 k$3@43@16)) (<= lo@7@16 k$3@43@16))
    (=>
      (and (<= k$3@43@16 hi@8@16) (<= lo@7@16 k$3@43@16))
      (and
        (<= k$3@43@16 hi@8@16)
        (<= lo@7@16 k$3@43@16)
        (or
          (not
            (<=
              lb@9@16
              ($FVF.lookup_val (as sm@44@16  $FVF<val>) (slot<Ref> a@6@16 k$3@43@16))))
          (<=
            lb@9@16
            ($FVF.lookup_val (as sm@44@16  $FVF<val>) (slot<Ref> a@6@16 k$3@43@16))))))
    (or
      (not (and (<= k$3@43@16 hi@8@16) (<= lo@7@16 k$3@43@16)))
      (and (<= k$3@43@16 hi@8@16) (<= lo@7@16 k$3@43@16))))
  :pattern ((slot<Ref> a@6@16 k$3@43@16))
  :qid |prog.l43-aux|)))
(assert (forall ((k$3@43@16 Int)) (!
  (=>
    (and (<= k$3@43@16 hi@8@16) (<= lo@7@16 k$3@43@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@46@16  $FVF<val>) (slot<Ref> a@6@16 k$3@43@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@44@16  $FVF<val>) (slot<Ref> a@6@16 k$3@43@16)))))
  :pattern ((slot<Ref> a@6@16 k$3@43@16))
  :qid |prog.l43|)))
(pop) ; 2
(push) ; 2
; [exec]
; var pivot: Int
(declare-const pivot@48@16 Int)
; [exec]
; var j: Int
(declare-const j@49@16 Int)
; [exec]
; var tmp2: Int
(declare-const tmp2@50@16 Int)
; [exec]
; pivot := slot(a, hi).val
; [eval] slot(a, hi)
(declare-const sm@51@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@51@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@51@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef24|)))
(declare-const pm@52@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@52@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@52@16  $FPM) r))
  :qid |qp.resPrmSumDef25|)))
(push) ; 3
(assert (not (< $Perm.No ($FVF.perm_val (as pm@52@16  $FPM) (slot<Ref> a@6@16 hi@8@16)))))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(declare-const pivot@53@16 Int)
(assert (=
  pivot@53@16
  ($FVF.lookup_val (as sm@51@16  $FVF<val>) (slot<Ref> a@6@16 hi@8@16))))
; [exec]
; i := lo - 1
; [eval] lo - 1
(declare-const i@54@16 Int)
(assert (= i@54@16 (- lo@7@16 1)))
; [exec]
; j := lo
(declare-const i@55@16 Int)
(declare-const tmp@56@16 Int)
(declare-const j@57@16 Int)
(push) ; 3
; Loop head block: Check well-definedness of invariant
(declare-const $t@58@16 $Snap)
(assert (= $t@58@16 ($Snap.combine ($Snap.first $t@58@16) ($Snap.second $t@58@16))))
(declare-const j$2@59@16 Int)
(push) ; 4
; [eval] 0 <= j$2 && j$2 < len(a)
; [eval] 0 <= j$2
(push) ; 5
; [then-branch: 16 | 0 <= j$2@59@16 | live]
; [else-branch: 16 | !(0 <= j$2@59@16) | live]
(push) ; 6
; [then-branch: 16 | 0 <= j$2@59@16]
(assert (<= 0 j$2@59@16))
; [eval] j$2 < len(a)
; [eval] len(a)
(pop) ; 6
(push) ; 6
; [else-branch: 16 | !(0 <= j$2@59@16)]
(assert (not (<= 0 j$2@59@16)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$2@59@16)) (<= 0 j$2@59@16)))
(assert (and (< j$2@59@16 (len<Int> a@6@16)) (<= 0 j$2@59@16)))
; [eval] slot(a, j$2)
(pop) ; 4
(declare-fun inv@60@16 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$2@59@16 Int)) (!
  (=>
    (and (< j$2@59@16 (len<Int> a@6@16)) (<= 0 j$2@59@16))
    (or (not (<= 0 j$2@59@16)) (<= 0 j$2@59@16)))
  :pattern ((slot<Ref> a@6@16 j$2@59@16))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 4
(assert (not (forall ((j$21@59@16 Int) (j$22@59@16 Int)) (!
  (=>
    (and
      (and (< j$21@59@16 (len<Int> a@6@16)) (<= 0 j$21@59@16))
      (and (< j$22@59@16 (len<Int> a@6@16)) (<= 0 j$22@59@16))
      (= (slot<Ref> a@6@16 j$21@59@16) (slot<Ref> a@6@16 j$22@59@16)))
    (= j$21@59@16 j$22@59@16))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$2@59@16 Int)) (!
  (=>
    (and (< j$2@59@16 (len<Int> a@6@16)) (<= 0 j$2@59@16))
    (= (inv@60@16 (slot<Ref> a@6@16 j$2@59@16)) j$2@59@16))
  :pattern ((slot<Ref> a@6@16 j$2@59@16))
  :qid |quant-u-15|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (= (slot<Ref> a@6@16 (inv@60@16 r)) r))
  :pattern ((inv@60@16 r))
  :qid |val-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j$2@59@16 Int)) (!
  (=>
    (and (< j$2@59@16 (len<Int> a@6@16)) (<= 0 j$2@59@16))
    (not (= (slot<Ref> a@6@16 j$2@59@16) $Ref.null)))
  :pattern ((slot<Ref> a@6@16 j$2@59@16))
  :qid |val-permImpliesNonNull|)))
(assert (=
  ($Snap.second $t@58@16)
  ($Snap.combine
    ($Snap.first ($Snap.second $t@58@16))
    ($Snap.second ($Snap.second $t@58@16)))))
(assert (= ($Snap.first ($Snap.second $t@58@16)) $Snap.unit))
; [eval] j >= lo
(assert (>= j@57@16 lo@7@16))
(assert (=
  ($Snap.second ($Snap.second $t@58@16))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second $t@58@16)))
    ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))
(assert (= ($Snap.first ($Snap.second ($Snap.second $t@58@16))) $Snap.unit))
; [eval] j <= hi
(assert (<= j@57@16 hi@8@16))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second $t@58@16)))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@58@16))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@58@16))))
  $Snap.unit))
; [eval] i >= lo - 1
; [eval] lo - 1
(assert (>= i@55@16 (- lo@7@16 1)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))
  $Snap.unit))
; [eval] i < j
(assert (< i@55@16 j@57@16))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))
  $Snap.unit))
; [eval] slot(a, hi).val == pivot
; [eval] slot(a, hi)
(declare-const sm@61@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@61@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@61@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef26|)))
(declare-const pm@62@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@62@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@62@16  $FPM) r))
  :qid |qp.resPrmSumDef27|)))
(push) ; 4
(assert (not (< $Perm.No ($FVF.perm_val (as pm@62@16  $FPM) (slot<Ref> a@6@16 hi@8@16)))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (=
  ($FVF.lookup_val (as sm@61@16  $FVF<val>) (slot<Ref> a@6@16 hi@8@16))
  pivot@53@16))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))
  $Snap.unit))
; [eval] (forall k: Int :: { slot(a, k) } k >= lo && k <= i ==> slot(a, k).val <= pivot)
(declare-const k@63@16 Int)
(push) ; 4
; [eval] k >= lo && k <= i ==> slot(a, k).val <= pivot
; [eval] k >= lo && k <= i
; [eval] k >= lo
(push) ; 5
; [then-branch: 17 | k@63@16 >= lo@7@16 | live]
; [else-branch: 17 | !(k@63@16 >= lo@7@16) | live]
(push) ; 6
; [then-branch: 17 | k@63@16 >= lo@7@16]
(assert (>= k@63@16 lo@7@16))
; [eval] k <= i
(pop) ; 6
(push) ; 6
; [else-branch: 17 | !(k@63@16 >= lo@7@16)]
(assert (not (>= k@63@16 lo@7@16)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@63@16 lo@7@16)) (>= k@63@16 lo@7@16)))
(push) ; 5
; [then-branch: 18 | k@63@16 <= i@55@16 && k@63@16 >= lo@7@16 | live]
; [else-branch: 18 | !(k@63@16 <= i@55@16 && k@63@16 >= lo@7@16) | live]
(push) ; 6
; [then-branch: 18 | k@63@16 <= i@55@16 && k@63@16 >= lo@7@16]
(assert (and (<= k@63@16 i@55@16) (>= k@63@16 lo@7@16)))
; [eval] slot(a, k).val <= pivot
; [eval] slot(a, k)
(declare-const sm@64@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@64@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@64@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef28|)))
(declare-const pm@65@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@65@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@65@16  $FPM) r))
  :qid |qp.resPrmSumDef29|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@65@16  $FPM) (slot<Ref> a@6@16 k@63@16)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 18 | !(k@63@16 <= i@55@16 && k@63@16 >= lo@7@16)]
(assert (not (and (<= k@63@16 i@55@16) (>= k@63@16 lo@7@16))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@64@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@64@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef28|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@65@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@65@16  $FPM) r))
  :qid |qp.resPrmSumDef29|)))
; Joined path conditions
(assert (or
  (not (and (<= k@63@16 i@55@16) (>= k@63@16 lo@7@16)))
  (and (<= k@63@16 i@55@16) (>= k@63@16 lo@7@16))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@64@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@64@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef28|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@65@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@65@16  $FPM) r))
  :qid |qp.resPrmSumDef29|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@63@16 Int)) (!
  (and
    (or (not (>= k@63@16 lo@7@16)) (>= k@63@16 lo@7@16))
    (or
      (not (and (<= k@63@16 i@55@16) (>= k@63@16 lo@7@16)))
      (and (<= k@63@16 i@55@16) (>= k@63@16 lo@7@16))))
  :pattern ((slot<Ref> a@6@16 k@63@16))
  :qid |prog.l54-aux|)))
(assert (forall ((k@63@16 Int)) (!
  (=>
    (and (<= k@63@16 i@55@16) (>= k@63@16 lo@7@16))
    (<=
      ($FVF.lookup_val (as sm@64@16  $FVF<val>) (slot<Ref> a@6@16 k@63@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@63@16))
  :qid |prog.l54|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))
  $Snap.unit))
; [eval] (forall k: Int :: { slot(a, k) } k >= i + 1 && k <= j - 1 ==> slot(a, k).val > pivot)
(declare-const k@66@16 Int)
(push) ; 4
; [eval] k >= i + 1 && k <= j - 1 ==> slot(a, k).val > pivot
; [eval] k >= i + 1 && k <= j - 1
; [eval] k >= i + 1
; [eval] i + 1
(push) ; 5
; [then-branch: 19 | k@66@16 >= i@55@16 + 1 | live]
; [else-branch: 19 | !(k@66@16 >= i@55@16 + 1) | live]
(push) ; 6
; [then-branch: 19 | k@66@16 >= i@55@16 + 1]
(assert (>= k@66@16 (+ i@55@16 1)))
; [eval] k <= j - 1
; [eval] j - 1
(pop) ; 6
(push) ; 6
; [else-branch: 19 | !(k@66@16 >= i@55@16 + 1)]
(assert (not (>= k@66@16 (+ i@55@16 1))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@66@16 (+ i@55@16 1))) (>= k@66@16 (+ i@55@16 1))))
(push) ; 5
; [then-branch: 20 | k@66@16 <= j@57@16 - 1 && k@66@16 >= i@55@16 + 1 | live]
; [else-branch: 20 | !(k@66@16 <= j@57@16 - 1 && k@66@16 >= i@55@16 + 1) | live]
(push) ; 6
; [then-branch: 20 | k@66@16 <= j@57@16 - 1 && k@66@16 >= i@55@16 + 1]
(assert (and (<= k@66@16 (- j@57@16 1)) (>= k@66@16 (+ i@55@16 1))))
; [eval] slot(a, k).val > pivot
; [eval] slot(a, k)
(declare-const sm@67@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@67@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@67@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef30|)))
(declare-const pm@68@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@68@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@68@16  $FPM) r))
  :qid |qp.resPrmSumDef31|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@68@16  $FPM) (slot<Ref> a@6@16 k@66@16)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 20 | !(k@66@16 <= j@57@16 - 1 && k@66@16 >= i@55@16 + 1)]
(assert (not (and (<= k@66@16 (- j@57@16 1)) (>= k@66@16 (+ i@55@16 1)))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@67@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@67@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef30|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@68@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@68@16  $FPM) r))
  :qid |qp.resPrmSumDef31|)))
; Joined path conditions
(assert (or
  (not (and (<= k@66@16 (- j@57@16 1)) (>= k@66@16 (+ i@55@16 1))))
  (and (<= k@66@16 (- j@57@16 1)) (>= k@66@16 (+ i@55@16 1)))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@67@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@67@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef30|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@68@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@68@16  $FPM) r))
  :qid |qp.resPrmSumDef31|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@66@16 Int)) (!
  (and
    (or (not (>= k@66@16 (+ i@55@16 1))) (>= k@66@16 (+ i@55@16 1)))
    (or
      (not (and (<= k@66@16 (- j@57@16 1)) (>= k@66@16 (+ i@55@16 1))))
      (and (<= k@66@16 (- j@57@16 1)) (>= k@66@16 (+ i@55@16 1)))))
  :pattern ((slot<Ref> a@6@16 k@66@16))
  :qid |prog.l55-aux|)))
(assert (forall ((k@66@16 Int)) (!
  (=>
    (and (<= k@66@16 (- j@57@16 1)) (>= k@66@16 (+ i@55@16 1)))
    (>
      ($FVF.lookup_val (as sm@67@16  $FVF<val>) (slot<Ref> a@6@16 k@66@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@66@16))
  :qid |prog.l55|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))
  $Snap.unit))
; [eval] (forall k$4: Int :: { slot(a, k$4) } 0 <= k$4 && k$4 <= lo - 1 ==> slot(a, k$4).val == old(slot(a, k$4).val))
(declare-const k$4@69@16 Int)
(push) ; 4
; [eval] 0 <= k$4 && k$4 <= lo - 1 ==> slot(a, k$4).val == old(slot(a, k$4).val)
; [eval] 0 <= k$4 && k$4 <= lo - 1
; [eval] 0 <= k$4
(push) ; 5
; [then-branch: 21 | 0 <= k$4@69@16 | live]
; [else-branch: 21 | !(0 <= k$4@69@16) | live]
(push) ; 6
; [then-branch: 21 | 0 <= k$4@69@16]
(assert (<= 0 k$4@69@16))
; [eval] k$4 <= lo - 1
; [eval] lo - 1
(pop) ; 6
(push) ; 6
; [else-branch: 21 | !(0 <= k$4@69@16)]
(assert (not (<= 0 k$4@69@16)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 k$4@69@16)) (<= 0 k$4@69@16)))
(push) ; 5
; [then-branch: 22 | k$4@69@16 <= lo@7@16 - 1 && 0 <= k$4@69@16 | live]
; [else-branch: 22 | !(k$4@69@16 <= lo@7@16 - 1 && 0 <= k$4@69@16) | live]
(push) ; 6
; [then-branch: 22 | k$4@69@16 <= lo@7@16 - 1 && 0 <= k$4@69@16]
(assert (and (<= k$4@69@16 (- lo@7@16 1)) (<= 0 k$4@69@16)))
; [eval] slot(a, k$4).val == old(slot(a, k$4).val)
; [eval] slot(a, k$4)
(declare-const sm@70@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@70@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@70@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef32|)))
(declare-const pm@71@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@71@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@71@16  $FPM) r))
  :qid |qp.resPrmSumDef33|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@71@16  $FPM) (slot<Ref> a@6@16 k$4@69@16)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$4).val)
; [eval] slot(a, k$4)
(declare-const sm@72@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@72@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@72@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef34|)))
(declare-const pm@73@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@73@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@73@16  $FPM) r))
  :qid |qp.resPrmSumDef35|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@73@16  $FPM) (slot<Ref> a@6@16 k$4@69@16)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 22 | !(k$4@69@16 <= lo@7@16 - 1 && 0 <= k$4@69@16)]
(assert (not (and (<= k$4@69@16 (- lo@7@16 1)) (<= 0 k$4@69@16))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@70@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@70@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef32|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@71@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@71@16  $FPM) r))
  :qid |qp.resPrmSumDef33|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@72@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@72@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef34|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@73@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@73@16  $FPM) r))
  :qid |qp.resPrmSumDef35|)))
; Joined path conditions
(assert (or
  (not (and (<= k$4@69@16 (- lo@7@16 1)) (<= 0 k$4@69@16)))
  (and (<= k$4@69@16 (- lo@7@16 1)) (<= 0 k$4@69@16))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@70@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@70@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef32|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@71@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@71@16  $FPM) r))
  :qid |qp.resPrmSumDef33|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@72@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@72@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef34|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@73@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@73@16  $FPM) r))
  :qid |qp.resPrmSumDef35|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$4@69@16 Int)) (!
  (and
    (or (not (<= 0 k$4@69@16)) (<= 0 k$4@69@16))
    (or
      (not (and (<= k$4@69@16 (- lo@7@16 1)) (<= 0 k$4@69@16)))
      (and (<= k$4@69@16 (- lo@7@16 1)) (<= 0 k$4@69@16))))
  :pattern ((slot<Ref> a@6@16 k$4@69@16))
  :qid |prog.l56-aux|)))
(assert (forall ((k$4@69@16 Int)) (!
  (=>
    (and (<= k$4@69@16 (- lo@7@16 1)) (<= 0 k$4@69@16))
    (=
      ($FVF.lookup_val (as sm@70@16  $FVF<val>) (slot<Ref> a@6@16 k$4@69@16))
      ($FVF.lookup_val (as sm@72@16  $FVF<val>) (slot<Ref> a@6@16 k$4@69@16))))
  :pattern ((slot<Ref> a@6@16 k$4@69@16))
  :qid |prog.l56|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))))
  $Snap.unit))
; [eval] (forall k$5: Int :: { slot(a, k$5) } hi + 1 <= k$5 && k$5 <= len(a) - 1 ==> slot(a, k$5).val == old(slot(a, k$5).val))
(declare-const k$5@74@16 Int)
(push) ; 4
; [eval] hi + 1 <= k$5 && k$5 <= len(a) - 1 ==> slot(a, k$5).val == old(slot(a, k$5).val)
; [eval] hi + 1 <= k$5 && k$5 <= len(a) - 1
; [eval] hi + 1 <= k$5
; [eval] hi + 1
(push) ; 5
; [then-branch: 23 | hi@8@16 + 1 <= k$5@74@16 | live]
; [else-branch: 23 | !(hi@8@16 + 1 <= k$5@74@16) | live]
(push) ; 6
; [then-branch: 23 | hi@8@16 + 1 <= k$5@74@16]
(assert (<= (+ hi@8@16 1) k$5@74@16))
; [eval] k$5 <= len(a) - 1
; [eval] len(a) - 1
; [eval] len(a)
(pop) ; 6
(push) ; 6
; [else-branch: 23 | !(hi@8@16 + 1 <= k$5@74@16)]
(assert (not (<= (+ hi@8@16 1) k$5@74@16)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= (+ hi@8@16 1) k$5@74@16)) (<= (+ hi@8@16 1) k$5@74@16)))
(push) ; 5
; [then-branch: 24 | k$5@74@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@74@16 | live]
; [else-branch: 24 | !(k$5@74@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@74@16) | live]
(push) ; 6
; [then-branch: 24 | k$5@74@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@74@16]
(assert (and (<= k$5@74@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@74@16)))
; [eval] slot(a, k$5).val == old(slot(a, k$5).val)
; [eval] slot(a, k$5)
(declare-const sm@75@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@75@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@75@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef36|)))
(declare-const pm@76@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@76@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@76@16  $FPM) r))
  :qid |qp.resPrmSumDef37|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@76@16  $FPM) (slot<Ref> a@6@16 k$5@74@16)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$5).val)
; [eval] slot(a, k$5)
(declare-const sm@77@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@77@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@77@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef38|)))
(declare-const pm@78@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@78@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@78@16  $FPM) r))
  :qid |qp.resPrmSumDef39|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@78@16  $FPM) (slot<Ref> a@6@16 k$5@74@16)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 24 | !(k$5@74@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@74@16)]
(assert (not (and (<= k$5@74@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@74@16))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@75@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@75@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef36|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@76@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@76@16  $FPM) r))
  :qid |qp.resPrmSumDef37|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@77@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@77@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef38|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@78@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@78@16  $FPM) r))
  :qid |qp.resPrmSumDef39|)))
; Joined path conditions
(assert (or
  (not (and (<= k$5@74@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@74@16)))
  (and (<= k$5@74@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@74@16))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@75@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@75@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef36|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@76@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@76@16  $FPM) r))
  :qid |qp.resPrmSumDef37|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@77@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@77@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef38|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@78@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@78@16  $FPM) r))
  :qid |qp.resPrmSumDef39|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$5@74@16 Int)) (!
  (and
    (or (not (<= (+ hi@8@16 1) k$5@74@16)) (<= (+ hi@8@16 1) k$5@74@16))
    (or
      (not
        (and (<= k$5@74@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@74@16)))
      (and (<= k$5@74@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@74@16))))
  :pattern ((slot<Ref> a@6@16 k$5@74@16))
  :qid |prog.l57-aux|)))
(assert (forall ((k$5@74@16 Int)) (!
  (=>
    (and (<= k$5@74@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@74@16))
    (=
      ($FVF.lookup_val (as sm@75@16  $FVF<val>) (slot<Ref> a@6@16 k$5@74@16))
      ($FVF.lookup_val (as sm@77@16  $FVF<val>) (slot<Ref> a@6@16 k$5@74@16))))
  :pattern ((slot<Ref> a@6@16 k$5@74@16))
  :qid |prog.l57|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))))
  $Snap.unit))
; [eval] (forall k$6: Int :: { slot(a, k$6) } lo <= k$6 && k$6 <= hi ==> lb <= slot(a, k$6).val && slot(a, k$6).val <= rb)
(declare-const k$6@79@16 Int)
(push) ; 4
; [eval] lo <= k$6 && k$6 <= hi ==> lb <= slot(a, k$6).val && slot(a, k$6).val <= rb
; [eval] lo <= k$6 && k$6 <= hi
; [eval] lo <= k$6
(push) ; 5
; [then-branch: 25 | lo@7@16 <= k$6@79@16 | live]
; [else-branch: 25 | !(lo@7@16 <= k$6@79@16) | live]
(push) ; 6
; [then-branch: 25 | lo@7@16 <= k$6@79@16]
(assert (<= lo@7@16 k$6@79@16))
; [eval] k$6 <= hi
(pop) ; 6
(push) ; 6
; [else-branch: 25 | !(lo@7@16 <= k$6@79@16)]
(assert (not (<= lo@7@16 k$6@79@16)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@7@16 k$6@79@16)) (<= lo@7@16 k$6@79@16)))
(push) ; 5
; [then-branch: 26 | k$6@79@16 <= hi@8@16 && lo@7@16 <= k$6@79@16 | live]
; [else-branch: 26 | !(k$6@79@16 <= hi@8@16 && lo@7@16 <= k$6@79@16) | live]
(push) ; 6
; [then-branch: 26 | k$6@79@16 <= hi@8@16 && lo@7@16 <= k$6@79@16]
(assert (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16)))
; [eval] lb <= slot(a, k$6).val && slot(a, k$6).val <= rb
; [eval] lb <= slot(a, k$6).val
; [eval] slot(a, k$6)
(declare-const sm@80@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@80@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@80@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef40|)))
(declare-const pm@81@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@81@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@81@16  $FPM) r))
  :qid |qp.resPrmSumDef41|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@81@16  $FPM) (slot<Ref> a@6@16 k$6@79@16)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch: 27 | lb@9@16 <= Lookup(val,sm@80@16,slot[Ref](a@6@16, k$6@79@16)) | live]
; [else-branch: 27 | !(lb@9@16 <= Lookup(val,sm@80@16,slot[Ref](a@6@16, k$6@79@16))) | live]
(push) ; 8
; [then-branch: 27 | lb@9@16 <= Lookup(val,sm@80@16,slot[Ref](a@6@16, k$6@79@16))]
(assert (<=
  lb@9@16
  ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16))))
; [eval] slot(a, k$6).val <= rb
; [eval] slot(a, k$6)
(declare-const sm@82@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@82@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@82@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef42|)))
(declare-const pm@83@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@83@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@83@16  $FPM) r))
  :qid |qp.resPrmSumDef43|)))
(push) ; 9
(assert (not (< $Perm.No ($FVF.perm_val (as pm@83@16  $FPM) (slot<Ref> a@6@16 k$6@79@16)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 27 | !(lb@9@16 <= Lookup(val,sm@80@16,slot[Ref](a@6@16, k$6@79@16)))]
(assert (not
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16)))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@82@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@82@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef42|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@83@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@83@16  $FPM) r))
  :qid |qp.resPrmSumDef43|)))
; Joined path conditions
(assert (or
  (not
    (<=
      lb@9@16
      ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16))))
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16)))))
(pop) ; 6
(push) ; 6
; [else-branch: 26 | !(k$6@79@16 <= hi@8@16 && lo@7@16 <= k$6@79@16)]
(assert (not (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@80@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@80@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef40|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@81@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@81@16  $FPM) r))
  :qid |qp.resPrmSumDef41|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@82@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@82@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef42|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@83@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@83@16  $FPM) r))
  :qid |qp.resPrmSumDef43|)))
(assert (=>
  (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16))
  (and
    (<= k$6@79@16 hi@8@16)
    (<= lo@7@16 k$6@79@16)
    (or
      (not
        (<=
          lb@9@16
          ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16))))
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16)))))))
; Joined path conditions
(assert (or
  (not (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16)))
  (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@80@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@80@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef40|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@81@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@81@16  $FPM) r))
  :qid |qp.resPrmSumDef41|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@82@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@82@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef42|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@83@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@83@16  $FPM) r))
  :qid |qp.resPrmSumDef43|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$6@79@16 Int)) (!
  (and
    (or (not (<= lo@7@16 k$6@79@16)) (<= lo@7@16 k$6@79@16))
    (=>
      (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16))
      (and
        (<= k$6@79@16 hi@8@16)
        (<= lo@7@16 k$6@79@16)
        (or
          (not
            (<=
              lb@9@16
              ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16))))
          (<=
            lb@9@16
            ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16))))))
    (or
      (not (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16)))
      (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16))))
  :pattern ((slot<Ref> a@6@16 k$6@79@16))
  :qid |prog.l58-aux|)))
(assert (forall ((k$6@79@16 Int)) (!
  (=>
    (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@82@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16)))))
  :pattern ((slot<Ref> a@6@16 k$6@79@16))
  :qid |prog.l58|)))
; Loop head block: Check well-definedness of edge conditions
(push) ; 4
; [eval] j <= hi - 1
; [eval] hi - 1
(pop) ; 4
(push) ; 4
; [eval] !(j <= hi - 1)
; [eval] j <= hi - 1
; [eval] hi - 1
(pop) ; 4
(pop) ; 3
(push) ; 3
; Loop head block: Establish invariant
(declare-const j$2@84@16 Int)
(push) ; 4
; [eval] 0 <= j$2 && j$2 < len(a)
; [eval] 0 <= j$2
(push) ; 5
; [then-branch: 28 | 0 <= j$2@84@16 | live]
; [else-branch: 28 | !(0 <= j$2@84@16) | live]
(push) ; 6
; [then-branch: 28 | 0 <= j$2@84@16]
(assert (<= 0 j$2@84@16))
; [eval] j$2 < len(a)
; [eval] len(a)
(pop) ; 6
(push) ; 6
; [else-branch: 28 | !(0 <= j$2@84@16)]
(assert (not (<= 0 j$2@84@16)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$2@84@16)) (<= 0 j$2@84@16)))
(assert (and (< j$2@84@16 (len<Int> a@6@16)) (<= 0 j$2@84@16)))
; [eval] slot(a, j$2)
(pop) ; 4
(declare-fun inv@85@16 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$2@84@16 Int)) (!
  (=>
    (and (< j$2@84@16 (len<Int> a@6@16)) (<= 0 j$2@84@16))
    (or (not (<= 0 j$2@84@16)) (<= 0 j$2@84@16)))
  :pattern ((slot<Ref> a@6@16 j$2@84@16))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 4
(assert (not (forall ((j$21@84@16 Int) (j$22@84@16 Int)) (!
  (=>
    (and
      (and (< j$21@84@16 (len<Int> a@6@16)) (<= 0 j$21@84@16))
      (and (< j$22@84@16 (len<Int> a@6@16)) (<= 0 j$22@84@16))
      (= (slot<Ref> a@6@16 j$21@84@16) (slot<Ref> a@6@16 j$22@84@16)))
    (= j$21@84@16 j$22@84@16))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$2@84@16 Int)) (!
  (=>
    (and (< j$2@84@16 (len<Int> a@6@16)) (<= 0 j$2@84@16))
    (= (inv@85@16 (slot<Ref> a@6@16 j$2@84@16)) j$2@84@16))
  :pattern ((slot<Ref> a@6@16 j$2@84@16))
  :qid |val-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@85@16 r) (len<Int> a@6@16)) (<= 0 (inv@85@16 r)))
    (= (slot<Ref> a@6@16 (inv@85@16 r)) r))
  :pattern ((inv@85@16 r))
  :qid |val-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@86@16 ((r $Ref)) $Perm
  (ite
    (and (< (inv@85@16 r) (len<Int> a@6@16)) (<= 0 (inv@85@16 r)))
    ($Perm.min
      (ite
        (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
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
        (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
        $Perm.Write
        $Perm.No)
      (pTaken@86@16 r))
    $Perm.No)
  
  :qid |quant-u-22|))))
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
    (and (< (inv@85@16 r) (len<Int> a@6@16)) (<= 0 (inv@85@16 r)))
    (= (- $Perm.Write (pTaken@86@16 r)) $Perm.No))
  
  :qid |quant-u-23|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@87@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@87@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@87@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef44|)))
; [eval] j >= lo
; [eval] j <= hi
; [eval] i >= lo - 1
; [eval] lo - 1
(set-option :timeout 0)
(push) ; 4
(assert (not (>= i@54@16 (- lo@7@16 1))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (>= i@54@16 (- lo@7@16 1)))
; [eval] i < j
(push) ; 4
(assert (not (< i@54@16 lo@7@16)))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (< i@54@16 lo@7@16))
; [eval] slot(a, hi).val == pivot
; [eval] slot(a, hi)
(push) ; 4
(assert (not (and
  (< (inv@14@16 (slot<Ref> a@6@16 hi@8@16)) (len<Int> a@6@16))
  (<= 0 (inv@14@16 (slot<Ref> a@6@16 hi@8@16))))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not (=
  ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 hi@8@16))
  pivot@53@16)))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (=
  ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 hi@8@16))
  pivot@53@16))
; [eval] (forall k: Int :: { slot(a, k) } k >= lo && k <= i ==> slot(a, k).val <= pivot)
(declare-const k@88@16 Int)
(push) ; 4
; [eval] k >= lo && k <= i ==> slot(a, k).val <= pivot
; [eval] k >= lo && k <= i
; [eval] k >= lo
(push) ; 5
; [then-branch: 29 | k@88@16 >= lo@7@16 | live]
; [else-branch: 29 | !(k@88@16 >= lo@7@16) | live]
(push) ; 6
; [then-branch: 29 | k@88@16 >= lo@7@16]
(assert (>= k@88@16 lo@7@16))
; [eval] k <= i
(pop) ; 6
(push) ; 6
; [else-branch: 29 | !(k@88@16 >= lo@7@16)]
(assert (not (>= k@88@16 lo@7@16)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@88@16 lo@7@16)) (>= k@88@16 lo@7@16)))
(push) ; 5
; [then-branch: 30 | k@88@16 <= i@54@16 && k@88@16 >= lo@7@16 | live]
; [else-branch: 30 | !(k@88@16 <= i@54@16 && k@88@16 >= lo@7@16) | live]
(push) ; 6
; [then-branch: 30 | k@88@16 <= i@54@16 && k@88@16 >= lo@7@16]
(assert (and (<= k@88@16 i@54@16) (>= k@88@16 lo@7@16)))
; [eval] slot(a, k).val <= pivot
; [eval] slot(a, k)
(push) ; 7
(assert (not (and
  (< (inv@14@16 (slot<Ref> a@6@16 k@88@16)) (len<Int> a@6@16))
  (<= 0 (inv@14@16 (slot<Ref> a@6@16 k@88@16))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 30 | !(k@88@16 <= i@54@16 && k@88@16 >= lo@7@16)]
(assert (not (and (<= k@88@16 i@54@16) (>= k@88@16 lo@7@16))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or
  (not (and (<= k@88@16 i@54@16) (>= k@88@16 lo@7@16)))
  (and (<= k@88@16 i@54@16) (>= k@88@16 lo@7@16))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@88@16 Int)) (!
  (and
    (or (not (>= k@88@16 lo@7@16)) (>= k@88@16 lo@7@16))
    (or
      (not (and (<= k@88@16 i@54@16) (>= k@88@16 lo@7@16)))
      (and (<= k@88@16 i@54@16) (>= k@88@16 lo@7@16))))
  :pattern ((slot<Ref> a@6@16 k@88@16))
  :qid |prog.l54-aux|)))
(push) ; 4
(assert (not (forall ((k@88@16 Int)) (!
  (=>
    (and (<= k@88@16 i@54@16) (>= k@88@16 lo@7@16))
    (<=
      ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k@88@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@88@16))
  :qid |prog.l54|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@88@16 Int)) (!
  (=>
    (and (<= k@88@16 i@54@16) (>= k@88@16 lo@7@16))
    (<=
      ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k@88@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@88@16))
  :qid |prog.l54|)))
; [eval] (forall k: Int :: { slot(a, k) } k >= i + 1 && k <= j - 1 ==> slot(a, k).val > pivot)
(declare-const k@89@16 Int)
(push) ; 4
; [eval] k >= i + 1 && k <= j - 1 ==> slot(a, k).val > pivot
; [eval] k >= i + 1 && k <= j - 1
; [eval] k >= i + 1
; [eval] i + 1
(push) ; 5
; [then-branch: 31 | k@89@16 >= i@54@16 + 1 | live]
; [else-branch: 31 | !(k@89@16 >= i@54@16 + 1) | live]
(push) ; 6
; [then-branch: 31 | k@89@16 >= i@54@16 + 1]
(assert (>= k@89@16 (+ i@54@16 1)))
; [eval] k <= j - 1
; [eval] j - 1
(pop) ; 6
(push) ; 6
; [else-branch: 31 | !(k@89@16 >= i@54@16 + 1)]
(assert (not (>= k@89@16 (+ i@54@16 1))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@89@16 (+ i@54@16 1))) (>= k@89@16 (+ i@54@16 1))))
(push) ; 5
; [then-branch: 32 | k@89@16 <= lo@7@16 - 1 && k@89@16 >= i@54@16 + 1 | live]
; [else-branch: 32 | !(k@89@16 <= lo@7@16 - 1 && k@89@16 >= i@54@16 + 1) | live]
(push) ; 6
; [then-branch: 32 | k@89@16 <= lo@7@16 - 1 && k@89@16 >= i@54@16 + 1]
(assert (and (<= k@89@16 (- lo@7@16 1)) (>= k@89@16 (+ i@54@16 1))))
; [eval] slot(a, k).val > pivot
; [eval] slot(a, k)
(push) ; 7
(assert (not (and
  (< (inv@14@16 (slot<Ref> a@6@16 k@89@16)) (len<Int> a@6@16))
  (<= 0 (inv@14@16 (slot<Ref> a@6@16 k@89@16))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 32 | !(k@89@16 <= lo@7@16 - 1 && k@89@16 >= i@54@16 + 1)]
(assert (not (and (<= k@89@16 (- lo@7@16 1)) (>= k@89@16 (+ i@54@16 1)))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or
  (not (and (<= k@89@16 (- lo@7@16 1)) (>= k@89@16 (+ i@54@16 1))))
  (and (<= k@89@16 (- lo@7@16 1)) (>= k@89@16 (+ i@54@16 1)))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@89@16 Int)) (!
  (and
    (or (not (>= k@89@16 (+ i@54@16 1))) (>= k@89@16 (+ i@54@16 1)))
    (or
      (not (and (<= k@89@16 (- lo@7@16 1)) (>= k@89@16 (+ i@54@16 1))))
      (and (<= k@89@16 (- lo@7@16 1)) (>= k@89@16 (+ i@54@16 1)))))
  :pattern ((slot<Ref> a@6@16 k@89@16))
  :qid |prog.l55-aux|)))
(push) ; 4
(assert (not (forall ((k@89@16 Int)) (!
  (=>
    (and (<= k@89@16 (- lo@7@16 1)) (>= k@89@16 (+ i@54@16 1)))
    (>
      ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k@89@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@89@16))
  :qid |prog.l55|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@89@16 Int)) (!
  (=>
    (and (<= k@89@16 (- lo@7@16 1)) (>= k@89@16 (+ i@54@16 1)))
    (>
      ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k@89@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@89@16))
  :qid |prog.l55|)))
; [eval] (forall k$4: Int :: { slot(a, k$4) } 0 <= k$4 && k$4 <= lo - 1 ==> slot(a, k$4).val == old(slot(a, k$4).val))
(declare-const k$4@90@16 Int)
(push) ; 4
; [eval] 0 <= k$4 && k$4 <= lo - 1 ==> slot(a, k$4).val == old(slot(a, k$4).val)
; [eval] 0 <= k$4 && k$4 <= lo - 1
; [eval] 0 <= k$4
(push) ; 5
; [then-branch: 33 | 0 <= k$4@90@16 | live]
; [else-branch: 33 | !(0 <= k$4@90@16) | live]
(push) ; 6
; [then-branch: 33 | 0 <= k$4@90@16]
(assert (<= 0 k$4@90@16))
; [eval] k$4 <= lo - 1
; [eval] lo - 1
(pop) ; 6
(push) ; 6
; [else-branch: 33 | !(0 <= k$4@90@16)]
(assert (not (<= 0 k$4@90@16)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 k$4@90@16)) (<= 0 k$4@90@16)))
(push) ; 5
; [then-branch: 34 | k$4@90@16 <= lo@7@16 - 1 && 0 <= k$4@90@16 | live]
; [else-branch: 34 | !(k$4@90@16 <= lo@7@16 - 1 && 0 <= k$4@90@16) | live]
(push) ; 6
; [then-branch: 34 | k$4@90@16 <= lo@7@16 - 1 && 0 <= k$4@90@16]
(assert (and (<= k$4@90@16 (- lo@7@16 1)) (<= 0 k$4@90@16)))
; [eval] slot(a, k$4).val == old(slot(a, k$4).val)
; [eval] slot(a, k$4)
(push) ; 7
(assert (not (and
  (< (inv@14@16 (slot<Ref> a@6@16 k$4@90@16)) (len<Int> a@6@16))
  (<= 0 (inv@14@16 (slot<Ref> a@6@16 k$4@90@16))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$4).val)
; [eval] slot(a, k$4)
(push) ; 7
(assert (not (and
  (< (inv@14@16 (slot<Ref> a@6@16 k$4@90@16)) (len<Int> a@6@16))
  (<= 0 (inv@14@16 (slot<Ref> a@6@16 k$4@90@16))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 34 | !(k$4@90@16 <= lo@7@16 - 1 && 0 <= k$4@90@16)]
(assert (not (and (<= k$4@90@16 (- lo@7@16 1)) (<= 0 k$4@90@16))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or
  (not (and (<= k$4@90@16 (- lo@7@16 1)) (<= 0 k$4@90@16)))
  (and (<= k$4@90@16 (- lo@7@16 1)) (<= 0 k$4@90@16))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$4@90@16 Int)) (!
  (and
    (or (not (<= 0 k$4@90@16)) (<= 0 k$4@90@16))
    (or
      (not (and (<= k$4@90@16 (- lo@7@16 1)) (<= 0 k$4@90@16)))
      (and (<= k$4@90@16 (- lo@7@16 1)) (<= 0 k$4@90@16))))
  :pattern ((slot<Ref> a@6@16 k$4@90@16))
  :qid |prog.l56-aux|)))
; [eval] (forall k$5: Int :: { slot(a, k$5) } hi + 1 <= k$5 && k$5 <= len(a) - 1 ==> slot(a, k$5).val == old(slot(a, k$5).val))
(declare-const k$5@91@16 Int)
(push) ; 4
; [eval] hi + 1 <= k$5 && k$5 <= len(a) - 1 ==> slot(a, k$5).val == old(slot(a, k$5).val)
; [eval] hi + 1 <= k$5 && k$5 <= len(a) - 1
; [eval] hi + 1 <= k$5
; [eval] hi + 1
(push) ; 5
; [then-branch: 35 | hi@8@16 + 1 <= k$5@91@16 | live]
; [else-branch: 35 | !(hi@8@16 + 1 <= k$5@91@16) | live]
(push) ; 6
; [then-branch: 35 | hi@8@16 + 1 <= k$5@91@16]
(assert (<= (+ hi@8@16 1) k$5@91@16))
; [eval] k$5 <= len(a) - 1
; [eval] len(a) - 1
; [eval] len(a)
(pop) ; 6
(push) ; 6
; [else-branch: 35 | !(hi@8@16 + 1 <= k$5@91@16)]
(assert (not (<= (+ hi@8@16 1) k$5@91@16)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= (+ hi@8@16 1) k$5@91@16)) (<= (+ hi@8@16 1) k$5@91@16)))
(push) ; 5
; [then-branch: 36 | k$5@91@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@91@16 | live]
; [else-branch: 36 | !(k$5@91@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@91@16) | live]
(push) ; 6
; [then-branch: 36 | k$5@91@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@91@16]
(assert (and (<= k$5@91@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@91@16)))
; [eval] slot(a, k$5).val == old(slot(a, k$5).val)
; [eval] slot(a, k$5)
(push) ; 7
(assert (not (and
  (< (inv@14@16 (slot<Ref> a@6@16 k$5@91@16)) (len<Int> a@6@16))
  (<= 0 (inv@14@16 (slot<Ref> a@6@16 k$5@91@16))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$5).val)
; [eval] slot(a, k$5)
(push) ; 7
(assert (not (and
  (< (inv@14@16 (slot<Ref> a@6@16 k$5@91@16)) (len<Int> a@6@16))
  (<= 0 (inv@14@16 (slot<Ref> a@6@16 k$5@91@16))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(push) ; 6
; [else-branch: 36 | !(k$5@91@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@91@16)]
(assert (not (and (<= k$5@91@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@91@16))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or
  (not (and (<= k$5@91@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@91@16)))
  (and (<= k$5@91@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@91@16))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$5@91@16 Int)) (!
  (and
    (or (not (<= (+ hi@8@16 1) k$5@91@16)) (<= (+ hi@8@16 1) k$5@91@16))
    (or
      (not
        (and (<= k$5@91@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@91@16)))
      (and (<= k$5@91@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@91@16))))
  :pattern ((slot<Ref> a@6@16 k$5@91@16))
  :qid |prog.l57-aux|)))
; [eval] (forall k$6: Int :: { slot(a, k$6) } lo <= k$6 && k$6 <= hi ==> lb <= slot(a, k$6).val && slot(a, k$6).val <= rb)
(declare-const k$6@92@16 Int)
(push) ; 4
; [eval] lo <= k$6 && k$6 <= hi ==> lb <= slot(a, k$6).val && slot(a, k$6).val <= rb
; [eval] lo <= k$6 && k$6 <= hi
; [eval] lo <= k$6
(push) ; 5
; [then-branch: 37 | lo@7@16 <= k$6@92@16 | live]
; [else-branch: 37 | !(lo@7@16 <= k$6@92@16) | live]
(push) ; 6
; [then-branch: 37 | lo@7@16 <= k$6@92@16]
(assert (<= lo@7@16 k$6@92@16))
; [eval] k$6 <= hi
(pop) ; 6
(push) ; 6
; [else-branch: 37 | !(lo@7@16 <= k$6@92@16)]
(assert (not (<= lo@7@16 k$6@92@16)))
(pop) ; 6
(pop) ; 5
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@7@16 k$6@92@16)) (<= lo@7@16 k$6@92@16)))
(push) ; 5
; [then-branch: 38 | k$6@92@16 <= hi@8@16 && lo@7@16 <= k$6@92@16 | live]
; [else-branch: 38 | !(k$6@92@16 <= hi@8@16 && lo@7@16 <= k$6@92@16) | live]
(push) ; 6
; [then-branch: 38 | k$6@92@16 <= hi@8@16 && lo@7@16 <= k$6@92@16]
(assert (and (<= k$6@92@16 hi@8@16) (<= lo@7@16 k$6@92@16)))
; [eval] lb <= slot(a, k$6).val && slot(a, k$6).val <= rb
; [eval] lb <= slot(a, k$6).val
; [eval] slot(a, k$6)
(push) ; 7
(assert (not (and
  (< (inv@14@16 (slot<Ref> a@6@16 k$6@92@16)) (len<Int> a@6@16))
  (<= 0 (inv@14@16 (slot<Ref> a@6@16 k$6@92@16))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch: 39 | lb@9@16 <= Lookup(val,sm@87@16,slot[Ref](a@6@16, k$6@92@16)) | live]
; [else-branch: 39 | !(lb@9@16 <= Lookup(val,sm@87@16,slot[Ref](a@6@16, k$6@92@16))) | live]
(push) ; 8
; [then-branch: 39 | lb@9@16 <= Lookup(val,sm@87@16,slot[Ref](a@6@16, k$6@92@16))]
(assert (<=
  lb@9@16
  ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16))))
; [eval] slot(a, k$6).val <= rb
; [eval] slot(a, k$6)
(push) ; 9
(assert (not (and
  (< (inv@14@16 (slot<Ref> a@6@16 k$6@92@16)) (len<Int> a@6@16))
  (<= 0 (inv@14@16 (slot<Ref> a@6@16 k$6@92@16))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 39 | !(lb@9@16 <= Lookup(val,sm@87@16,slot[Ref](a@6@16, k$6@92@16)))]
(assert (not
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16)))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (<=
      lb@9@16
      ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16))))
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16)))))
(pop) ; 6
(push) ; 6
; [else-branch: 38 | !(k$6@92@16 <= hi@8@16 && lo@7@16 <= k$6@92@16)]
(assert (not (and (<= k$6@92@16 hi@8@16) (<= lo@7@16 k$6@92@16))))
(pop) ; 6
(pop) ; 5
; Joined path conditions
(assert (=>
  (and (<= k$6@92@16 hi@8@16) (<= lo@7@16 k$6@92@16))
  (and
    (<= k$6@92@16 hi@8@16)
    (<= lo@7@16 k$6@92@16)
    (or
      (not
        (<=
          lb@9@16
          ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16))))
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16)))))))
; Joined path conditions
(assert (or
  (not (and (<= k$6@92@16 hi@8@16) (<= lo@7@16 k$6@92@16)))
  (and (<= k$6@92@16 hi@8@16) (<= lo@7@16 k$6@92@16))))
(pop) ; 4
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$6@92@16 Int)) (!
  (and
    (or (not (<= lo@7@16 k$6@92@16)) (<= lo@7@16 k$6@92@16))
    (=>
      (and (<= k$6@92@16 hi@8@16) (<= lo@7@16 k$6@92@16))
      (and
        (<= k$6@92@16 hi@8@16)
        (<= lo@7@16 k$6@92@16)
        (or
          (not
            (<=
              lb@9@16
              ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16))))
          (<=
            lb@9@16
            ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16))))))
    (or
      (not (and (<= k$6@92@16 hi@8@16) (<= lo@7@16 k$6@92@16)))
      (and (<= k$6@92@16 hi@8@16) (<= lo@7@16 k$6@92@16))))
  :pattern ((slot<Ref> a@6@16 k$6@92@16))
  :qid |prog.l58-aux|)))
(push) ; 4
(assert (not (forall ((k$6@92@16 Int)) (!
  (=>
    (and (<= k$6@92@16 hi@8@16) (<= lo@7@16 k$6@92@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16)))))
  :pattern ((slot<Ref> a@6@16 k$6@92@16))
  :qid |prog.l58|))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k$6@92@16 Int)) (!
  (=>
    (and (<= k$6@92@16 hi@8@16) (<= lo@7@16 k$6@92@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@87@16  $FVF<val>) (slot<Ref> a@6@16 k$6@92@16)))))
  :pattern ((slot<Ref> a@6@16 k$6@92@16))
  :qid |prog.l58|)))
; Loop head block: Execute statements of loop head block (in invariant state)
(push) ; 4
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (= (slot<Ref> a@6@16 (inv@60@16 r)) r))
  :pattern ((inv@60@16 r))
  :qid |val-fctOfInv|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@61@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@61@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef26|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@62@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@62@16  $FPM) r))
  :qid |qp.resPrmSumDef27|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@64@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@64@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef28|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@65@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@65@16  $FPM) r))
  :qid |qp.resPrmSumDef29|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@67@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@67@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef30|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@68@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@68@16  $FPM) r))
  :qid |qp.resPrmSumDef31|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@70@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@70@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef32|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@71@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@71@16  $FPM) r))
  :qid |qp.resPrmSumDef33|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@72@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@72@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef34|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@73@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@73@16  $FPM) r))
  :qid |qp.resPrmSumDef35|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@75@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@75@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef36|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@76@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@76@16  $FPM) r))
  :qid |qp.resPrmSumDef37|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@77@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@77@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef38|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@78@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@78@16  $FPM) r))
  :qid |qp.resPrmSumDef39|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@80@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@80@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef40|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@81@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@81@16  $FPM) r))
  :qid |qp.resPrmSumDef41|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@82@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@82@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef42|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@83@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@83@16  $FPM) r))
  :qid |qp.resPrmSumDef43|)))
(assert (forall ((j$2@59@16 Int)) (!
  (=>
    (and (< j$2@59@16 (len<Int> a@6@16)) (<= 0 j$2@59@16))
    (= (inv@60@16 (slot<Ref> a@6@16 j$2@59@16)) j$2@59@16))
  :pattern ((slot<Ref> a@6@16 j$2@59@16))
  :qid |quant-u-15|)))
(assert (forall ((j$2@59@16 Int)) (!
  (=>
    (and (< j$2@59@16 (len<Int> a@6@16)) (<= 0 j$2@59@16))
    (not (= (slot<Ref> a@6@16 j$2@59@16) $Ref.null)))
  :pattern ((slot<Ref> a@6@16 j$2@59@16))
  :qid |val-permImpliesNonNull|)))
(assert (=
  ($Snap.second $t@58@16)
  ($Snap.combine
    ($Snap.first ($Snap.second $t@58@16))
    ($Snap.second ($Snap.second $t@58@16)))))
(assert (= ($Snap.first ($Snap.second $t@58@16)) $Snap.unit))
(assert (>= j@57@16 lo@7@16))
(assert (=
  ($Snap.second ($Snap.second $t@58@16))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second $t@58@16)))
    ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))
(assert (= ($Snap.first ($Snap.second ($Snap.second $t@58@16))) $Snap.unit))
(assert (<= j@57@16 hi@8@16))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second $t@58@16)))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@58@16))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@58@16))))
  $Snap.unit))
(assert (>= i@55@16 (- lo@7@16 1)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))
  $Snap.unit))
(assert (< i@55@16 j@57@16))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))
  $Snap.unit))
(assert (=
  ($FVF.lookup_val (as sm@61@16  $FVF<val>) (slot<Ref> a@6@16 hi@8@16))
  pivot@53@16))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))
  $Snap.unit))
(assert (forall ((k@63@16 Int)) (!
  (and
    (or (not (>= k@63@16 lo@7@16)) (>= k@63@16 lo@7@16))
    (or
      (not (and (<= k@63@16 i@55@16) (>= k@63@16 lo@7@16)))
      (and (<= k@63@16 i@55@16) (>= k@63@16 lo@7@16))))
  :pattern ((slot<Ref> a@6@16 k@63@16))
  :qid |prog.l54-aux|)))
(assert (forall ((k@63@16 Int)) (!
  (=>
    (and (<= k@63@16 i@55@16) (>= k@63@16 lo@7@16))
    (<=
      ($FVF.lookup_val (as sm@64@16  $FVF<val>) (slot<Ref> a@6@16 k@63@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@63@16))
  :qid |prog.l54|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))
  $Snap.unit))
(assert (forall ((k@66@16 Int)) (!
  (and
    (or (not (>= k@66@16 (+ i@55@16 1))) (>= k@66@16 (+ i@55@16 1)))
    (or
      (not (and (<= k@66@16 (- j@57@16 1)) (>= k@66@16 (+ i@55@16 1))))
      (and (<= k@66@16 (- j@57@16 1)) (>= k@66@16 (+ i@55@16 1)))))
  :pattern ((slot<Ref> a@6@16 k@66@16))
  :qid |prog.l55-aux|)))
(assert (forall ((k@66@16 Int)) (!
  (=>
    (and (<= k@66@16 (- j@57@16 1)) (>= k@66@16 (+ i@55@16 1)))
    (>
      ($FVF.lookup_val (as sm@67@16  $FVF<val>) (slot<Ref> a@6@16 k@66@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@66@16))
  :qid |prog.l55|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))
  $Snap.unit))
(assert (forall ((k$4@69@16 Int)) (!
  (and
    (or (not (<= 0 k$4@69@16)) (<= 0 k$4@69@16))
    (or
      (not (and (<= k$4@69@16 (- lo@7@16 1)) (<= 0 k$4@69@16)))
      (and (<= k$4@69@16 (- lo@7@16 1)) (<= 0 k$4@69@16))))
  :pattern ((slot<Ref> a@6@16 k$4@69@16))
  :qid |prog.l56-aux|)))
(assert (forall ((k$4@69@16 Int)) (!
  (=>
    (and (<= k$4@69@16 (- lo@7@16 1)) (<= 0 k$4@69@16))
    (=
      ($FVF.lookup_val (as sm@70@16  $FVF<val>) (slot<Ref> a@6@16 k$4@69@16))
      ($FVF.lookup_val (as sm@72@16  $FVF<val>) (slot<Ref> a@6@16 k$4@69@16))))
  :pattern ((slot<Ref> a@6@16 k$4@69@16))
  :qid |prog.l56|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16)))))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))))
  $Snap.unit))
(assert (forall ((k$5@74@16 Int)) (!
  (and
    (or (not (<= (+ hi@8@16 1) k$5@74@16)) (<= (+ hi@8@16 1) k$5@74@16))
    (or
      (not
        (and (<= k$5@74@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@74@16)))
      (and (<= k$5@74@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@74@16))))
  :pattern ((slot<Ref> a@6@16 k$5@74@16))
  :qid |prog.l57-aux|)))
(assert (forall ((k$5@74@16 Int)) (!
  (=>
    (and (<= k$5@74@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@74@16))
    (=
      ($FVF.lookup_val (as sm@75@16  $FVF<val>) (slot<Ref> a@6@16 k$5@74@16))
      ($FVF.lookup_val (as sm@77@16  $FVF<val>) (slot<Ref> a@6@16 k$5@74@16))))
  :pattern ((slot<Ref> a@6@16 k$5@74@16))
  :qid |prog.l57|)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@58@16))))))))))
  $Snap.unit))
(assert (forall ((k$6@79@16 Int)) (!
  (and
    (or (not (<= lo@7@16 k$6@79@16)) (<= lo@7@16 k$6@79@16))
    (=>
      (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16))
      (and
        (<= k$6@79@16 hi@8@16)
        (<= lo@7@16 k$6@79@16)
        (or
          (not
            (<=
              lb@9@16
              ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16))))
          (<=
            lb@9@16
            ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16))))))
    (or
      (not (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16)))
      (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16))))
  :pattern ((slot<Ref> a@6@16 k$6@79@16))
  :qid |prog.l58-aux|)))
(assert (forall ((k$6@79@16 Int)) (!
  (=>
    (and (<= k$6@79@16 hi@8@16) (<= lo@7@16 k$6@79@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@82@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@80@16  $FVF<val>) (slot<Ref> a@6@16 k$6@79@16)))))
  :pattern ((slot<Ref> a@6@16 k$6@79@16))
  :qid |prog.l58|)))
(assert (= $t@58@16 ($Snap.combine ($Snap.first $t@58@16) ($Snap.second $t@58@16))))
(assert (forall ((j$2@59@16 Int)) (!
  (=>
    (and (< j$2@59@16 (len<Int> a@6@16)) (<= 0 j$2@59@16))
    (or (not (<= 0 j$2@59@16)) (<= 0 j$2@59@16)))
  :pattern ((slot<Ref> a@6@16 j$2@59@16))
  :qid |val-aux|)))
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
(set-option :timeout 10)
(check-sat)
; unknown
; Loop head block: Follow loop-internal edges
; [eval] j <= hi - 1
; [eval] hi - 1
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (not (<= j@57@16 (- hi@8@16 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (<= j@57@16 (- hi@8@16 1))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [then-branch: 40 | j@57@16 <= hi@8@16 - 1 | live]
; [else-branch: 40 | !(j@57@16 <= hi@8@16 - 1) | live]
(set-option :timeout 0)
(push) ; 5
; [then-branch: 40 | j@57@16 <= hi@8@16 - 1]
(assert (<= j@57@16 (- hi@8@16 1)))
; [eval] slot(a, j).val <= pivot
; [eval] slot(a, j)
(declare-const sm@93@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@93@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@93@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef45|)))
(declare-const pm@94@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@94@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@94@16  $FPM) r))
  :qid |qp.resPrmSumDef46|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@94@16  $FPM) (slot<Ref> a@6@16 j@57@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(set-option :timeout 10)
(assert (not (not
  (<=
    ($FVF.lookup_val (as sm@93@16  $FVF<val>) (slot<Ref> a@6@16 j@57@16))
    pivot@53@16))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 10)
(assert (not (<=
  ($FVF.lookup_val (as sm@93@16  $FVF<val>) (slot<Ref> a@6@16 j@57@16))
  pivot@53@16)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [then-branch: 41 | Lookup(val,sm@93@16,slot[Ref](a@6@16, j@57@16)) <= pivot@53@16 | live]
; [else-branch: 41 | !(Lookup(val,sm@93@16,slot[Ref](a@6@16, j@57@16)) <= pivot@53@16) | live]
(set-option :timeout 0)
(push) ; 6
; [then-branch: 41 | Lookup(val,sm@93@16,slot[Ref](a@6@16, j@57@16)) <= pivot@53@16]
(assert (<=
  ($FVF.lookup_val (as sm@93@16  $FVF<val>) (slot<Ref> a@6@16 j@57@16))
  pivot@53@16))
; [exec]
; var tmp: Int
(declare-const tmp@95@16 Int)
; [exec]
; i := i + 1
; [eval] i + 1
(declare-const i@96@16 Int)
(assert (= i@96@16 (+ i@55@16 1)))
; [exec]
; tmp := slot(a, i).val
; [eval] slot(a, i)
(declare-const sm@97@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@97@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@97@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef47|)))
(declare-const pm@98@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@98@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@98@16  $FPM) r))
  :qid |qp.resPrmSumDef48|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@98@16  $FPM) (slot<Ref> a@6@16 i@96@16)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const tmp@99@16 Int)
(assert (=
  tmp@99@16
  ($FVF.lookup_val (as sm@97@16  $FVF<val>) (slot<Ref> a@6@16 i@96@16))))
; [exec]
; slot(a, i).val := slot(a, j).val
; [eval] slot(a, i)
; [eval] slot(a, j)
(declare-const sm@100@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@100@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@100@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef49|)))
(declare-const pm@101@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@101@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@101@16  $FPM) r))
  :qid |qp.resPrmSumDef50|)))
(push) ; 7
(assert (not (< $Perm.No ($FVF.perm_val (as pm@101@16  $FPM) (slot<Ref> a@6@16 j@57@16)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Precomputing data for removing quantified permissions
(define-fun pTaken@102@16 ((r $Ref)) $Perm
  (ite
    (= r (slot<Ref> a@6@16 i@96@16))
    ($Perm.min
      (ite
        (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
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
(push) ; 7
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (ite
        (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
        $Perm.Write
        $Perm.No)
      (pTaken@102@16 r))
    $Perm.No)
  
  :qid |quant-u-31|))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (= r (slot<Ref> a@6@16 i@96@16))
    (= (- $Perm.Write (pTaken@102@16 r)) $Perm.No))
  
  :qid |quant-u-32|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@103@16 $FVF<val>)
; Definitional axioms for singleton-FVF's value
(assert (=
  ($FVF.lookup_val (as sm@103@16  $FVF<val>) (slot<Ref> a@6@16 i@96@16))
  ($FVF.lookup_val (as sm@100@16  $FVF<val>) (slot<Ref> a@6@16 j@57@16))))
; [exec]
; slot(a, j).val := tmp
; [eval] slot(a, j)
; Precomputing data for removing quantified permissions
(define-fun pTaken@104@16 ((r $Ref)) $Perm
  (ite
    (= r (slot<Ref> a@6@16 j@57@16))
    ($Perm.min
      (ite (= r (slot<Ref> a@6@16 i@96@16)) $Perm.Write $Perm.No)
      $Perm.Write)
    $Perm.No))
(define-fun pTaken@105@16 ((r $Ref)) $Perm
  (ite
    (= r (slot<Ref> a@6@16 j@57@16))
    ($Perm.min
      (-
        (ite
          (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
          $Perm.Write
          $Perm.No)
        (pTaken@102@16 r))
      (- $Perm.Write (pTaken@104@16 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Chunk depleted?
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (=
  (-
    (ite
      (= (slot<Ref> a@6@16 i@96@16) (slot<Ref> a@6@16 i@96@16))
      $Perm.Write
      $Perm.No)
    (pTaken@104@16 (slot<Ref> a@6@16 i@96@16)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (= r (slot<Ref> a@6@16 j@57@16))
    (= (- $Perm.Write (pTaken@104@16 r)) $Perm.No))
  
  :qid |quant-u-35|))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (-
        (ite
          (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
          $Perm.Write
          $Perm.No)
        (pTaken@102@16 r))
      (pTaken@105@16 r))
    $Perm.No)
  
  :qid |quant-u-36|))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (= r (slot<Ref> a@6@16 j@57@16))
    (= (- (- $Perm.Write (pTaken@104@16 r)) (pTaken@105@16 r)) $Perm.No))
  
  :qid |quant-u-37|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@106@16 $FVF<val>)
; Definitional axioms for singleton-FVF's value
(assert (=
  ($FVF.lookup_val (as sm@106@16  $FVF<val>) (slot<Ref> a@6@16 j@57@16))
  tmp@99@16))
; [exec]
; j := j + 1
; [eval] j + 1
(declare-const j@107@16 Int)
(assert (= j@107@16 (+ j@57@16 1)))
; Loop head block: Re-establish invariant
(declare-const j$2@108@16 Int)
(set-option :timeout 0)
(push) ; 7
; [eval] 0 <= j$2 && j$2 < len(a)
; [eval] 0 <= j$2
(push) ; 8
; [then-branch: 42 | 0 <= j$2@108@16 | live]
; [else-branch: 42 | !(0 <= j$2@108@16) | live]
(push) ; 9
; [then-branch: 42 | 0 <= j$2@108@16]
(assert (<= 0 j$2@108@16))
; [eval] j$2 < len(a)
; [eval] len(a)
(pop) ; 9
(push) ; 9
; [else-branch: 42 | !(0 <= j$2@108@16)]
(assert (not (<= 0 j$2@108@16)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$2@108@16)) (<= 0 j$2@108@16)))
(assert (and (< j$2@108@16 (len<Int> a@6@16)) (<= 0 j$2@108@16)))
; [eval] slot(a, j$2)
(pop) ; 7
(declare-fun inv@109@16 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$2@108@16 Int)) (!
  (=>
    (and (< j$2@108@16 (len<Int> a@6@16)) (<= 0 j$2@108@16))
    (or (not (<= 0 j$2@108@16)) (<= 0 j$2@108@16)))
  :pattern ((slot<Ref> a@6@16 j$2@108@16))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 7
(assert (not (forall ((j$21@108@16 Int) (j$22@108@16 Int)) (!
  (=>
    (and
      (and (< j$21@108@16 (len<Int> a@6@16)) (<= 0 j$21@108@16))
      (and (< j$22@108@16 (len<Int> a@6@16)) (<= 0 j$22@108@16))
      (= (slot<Ref> a@6@16 j$21@108@16) (slot<Ref> a@6@16 j$22@108@16)))
    (= j$21@108@16 j$22@108@16))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$2@108@16 Int)) (!
  (=>
    (and (< j$2@108@16 (len<Int> a@6@16)) (<= 0 j$2@108@16))
    (= (inv@109@16 (slot<Ref> a@6@16 j$2@108@16)) j$2@108@16))
  :pattern ((slot<Ref> a@6@16 j$2@108@16))
  :qid |val-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@109@16 r) (len<Int> a@6@16)) (<= 0 (inv@109@16 r)))
    (= (slot<Ref> a@6@16 (inv@109@16 r)) r))
  :pattern ((inv@109@16 r))
  :qid |val-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@110@16 ((r $Ref)) $Perm
  (ite
    (and (< (inv@109@16 r) (len<Int> a@6@16)) (<= 0 (inv@109@16 r)))
    ($Perm.min
      (ite (= r (slot<Ref> a@6@16 j@57@16)) $Perm.Write $Perm.No)
      $Perm.Write)
    $Perm.No))
(define-fun pTaken@111@16 ((r $Ref)) $Perm
  (ite
    (and (< (inv@109@16 r) (len<Int> a@6@16)) (<= 0 (inv@109@16 r)))
    ($Perm.min
      (-
        (-
          (ite
            (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
            $Perm.Write
            $Perm.No)
          (pTaken@102@16 r))
        (pTaken@105@16 r))
      (- $Perm.Write (pTaken@110@16 r)))
    $Perm.No))
(define-fun pTaken@112@16 ((r $Ref)) $Perm
  (ite
    (and (< (inv@109@16 r) (len<Int> a@6@16)) (<= 0 (inv@109@16 r)))
    ($Perm.min
      (-
        (ite (= r (slot<Ref> a@6@16 i@96@16)) $Perm.Write $Perm.No)
        (pTaken@104@16 r))
      (- (- $Perm.Write (pTaken@110@16 r)) (pTaken@111@16 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Chunk depleted?
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (=
  (-
    (ite
      (= (slot<Ref> a@6@16 j@57@16) (slot<Ref> a@6@16 j@57@16))
      $Perm.Write
      $Perm.No)
    (pTaken@110@16 (slot<Ref> a@6@16 j@57@16)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (and (< (inv@109@16 r) (len<Int> a@6@16)) (<= 0 (inv@109@16 r)))
    (= (- $Perm.Write (pTaken@110@16 r)) $Perm.No))
  
  :qid |quant-u-41|))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (-
        (-
          (ite
            (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
            $Perm.Write
            $Perm.No)
          (pTaken@102@16 r))
        (pTaken@105@16 r))
      (pTaken@111@16 r))
    $Perm.No)
  
  :qid |quant-u-42|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (and (< (inv@109@16 r) (len<Int> a@6@16)) (<= 0 (inv@109@16 r)))
    (= (- (- $Perm.Write (pTaken@110@16 r)) (pTaken@111@16 r)) $Perm.No))
  
  :qid |quant-u-43|))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (=
  (-
    (-
      (ite
        (= (slot<Ref> a@6@16 i@96@16) (slot<Ref> a@6@16 i@96@16))
        $Perm.Write
        $Perm.No)
      (pTaken@104@16 (slot<Ref> a@6@16 i@96@16)))
    (pTaken@112@16 (slot<Ref> a@6@16 i@96@16)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (and (< (inv@109@16 r) (len<Int> a@6@16)) (<= 0 (inv@109@16 r)))
    (=
      (-
        (- (- $Perm.Write (pTaken@110@16 r)) (pTaken@111@16 r))
        (pTaken@112@16 r))
      $Perm.No))
  
  :qid |quant-u-45|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@113@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (= r (slot<Ref> a@6@16 j@57@16))
    (=
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) r)
      ($FVF.lookup_val (as sm@106@16  $FVF<val>) r)))
  :pattern (($FVF.lookup_val (as sm@113@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val (as sm@106@16  $FVF<val>) r))
  :qid |qp.fvfValDef51|)))
(assert (forall ((r $Ref)) (!
  (=>
    (<
      $Perm.No
      (-
        (-
          (ite
            (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
            $Perm.Write
            $Perm.No)
          (pTaken@102@16 r))
        (pTaken@105@16 r)))
    (=
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@113@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef52|)))
(assert (forall ((r $Ref)) (!
  (=>
    (<
      $Perm.No
      (-
        (ite (= r (slot<Ref> a@6@16 i@96@16)) $Perm.Write $Perm.No)
        (pTaken@104@16 r)))
    (=
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) r)
      ($FVF.lookup_val (as sm@103@16  $FVF<val>) r)))
  :pattern (($FVF.lookup_val (as sm@113@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val (as sm@103@16  $FVF<val>) r))
  :qid |qp.fvfValDef53|)))
; [eval] j >= lo
(set-option :timeout 0)
(push) ; 7
(assert (not (>= j@107@16 lo@7@16)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (>= j@107@16 lo@7@16))
; [eval] j <= hi
(push) ; 7
(assert (not (<= j@107@16 hi@8@16)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (<= j@107@16 hi@8@16))
; [eval] i >= lo - 1
; [eval] lo - 1
(push) ; 7
(assert (not (>= i@96@16 (- lo@7@16 1))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (>= i@96@16 (- lo@7@16 1)))
; [eval] i < j
(push) ; 7
(assert (not (< i@96@16 j@107@16)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< i@96@16 j@107@16))
; [eval] slot(a, hi).val == pivot
; [eval] slot(a, hi)
(push) ; 7
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 hi@8@16) (slot<Ref> a@6@16 j@57@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 hi@8@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 hi@8@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@102@16 (slot<Ref> a@6@16 hi@8@16)))
        (pTaken@105@16 (slot<Ref> a@6@16 hi@8@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 hi@8@16) (slot<Ref> a@6@16 i@96@16))
        $Perm.Write
        $Perm.No)
      (pTaken@104@16 (slot<Ref> a@6@16 hi@8@16)))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (=
  ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 hi@8@16))
  pivot@53@16)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (=
  ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 hi@8@16))
  pivot@53@16))
; [eval] (forall k: Int :: { slot(a, k) } k >= lo && k <= i ==> slot(a, k).val <= pivot)
(declare-const k@114@16 Int)
(push) ; 7
; [eval] k >= lo && k <= i ==> slot(a, k).val <= pivot
; [eval] k >= lo && k <= i
; [eval] k >= lo
(push) ; 8
; [then-branch: 43 | k@114@16 >= lo@7@16 | live]
; [else-branch: 43 | !(k@114@16 >= lo@7@16) | live]
(push) ; 9
; [then-branch: 43 | k@114@16 >= lo@7@16]
(assert (>= k@114@16 lo@7@16))
; [eval] k <= i
(pop) ; 9
(push) ; 9
; [else-branch: 43 | !(k@114@16 >= lo@7@16)]
(assert (not (>= k@114@16 lo@7@16)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@114@16 lo@7@16)) (>= k@114@16 lo@7@16)))
(push) ; 8
; [then-branch: 44 | k@114@16 <= i@96@16 && k@114@16 >= lo@7@16 | live]
; [else-branch: 44 | !(k@114@16 <= i@96@16 && k@114@16 >= lo@7@16) | live]
(push) ; 9
; [then-branch: 44 | k@114@16 <= i@96@16 && k@114@16 >= lo@7@16]
(assert (and (<= k@114@16 i@96@16) (>= k@114@16 lo@7@16)))
; [eval] slot(a, k).val <= pivot
; [eval] slot(a, k)
(push) ; 10
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k@114@16) (slot<Ref> a@6@16 j@57@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k@114@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k@114@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@102@16 (slot<Ref> a@6@16 k@114@16)))
        (pTaken@105@16 (slot<Ref> a@6@16 k@114@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k@114@16) (slot<Ref> a@6@16 i@96@16))
        $Perm.Write
        $Perm.No)
      (pTaken@104@16 (slot<Ref> a@6@16 k@114@16)))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(pop) ; 9
(push) ; 9
; [else-branch: 44 | !(k@114@16 <= i@96@16 && k@114@16 >= lo@7@16)]
(assert (not (and (<= k@114@16 i@96@16) (>= k@114@16 lo@7@16))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or
  (not (and (<= k@114@16 i@96@16) (>= k@114@16 lo@7@16)))
  (and (<= k@114@16 i@96@16) (>= k@114@16 lo@7@16))))
(pop) ; 7
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@114@16 Int)) (!
  (and
    (or (not (>= k@114@16 lo@7@16)) (>= k@114@16 lo@7@16))
    (or
      (not (and (<= k@114@16 i@96@16) (>= k@114@16 lo@7@16)))
      (and (<= k@114@16 i@96@16) (>= k@114@16 lo@7@16))))
  :pattern ((slot<Ref> a@6@16 k@114@16))
  :qid |prog.l54-aux|)))
(push) ; 7
(assert (not (forall ((k@114@16 Int)) (!
  (=>
    (and (<= k@114@16 i@96@16) (>= k@114@16 lo@7@16))
    (<=
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k@114@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@114@16))
  :qid |prog.l54|))))
(check-sat)
; unsat
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
(assert (forall ((k@114@16 Int)) (!
  (=>
    (and (<= k@114@16 i@96@16) (>= k@114@16 lo@7@16))
    (<=
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k@114@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@114@16))
  :qid |prog.l54|)))
; [eval] (forall k: Int :: { slot(a, k) } k >= i + 1 && k <= j - 1 ==> slot(a, k).val > pivot)
(declare-const k@115@16 Int)
(push) ; 7
; [eval] k >= i + 1 && k <= j - 1 ==> slot(a, k).val > pivot
; [eval] k >= i + 1 && k <= j - 1
; [eval] k >= i + 1
; [eval] i + 1
(push) ; 8
; [then-branch: 45 | k@115@16 >= i@96@16 + 1 | live]
; [else-branch: 45 | !(k@115@16 >= i@96@16 + 1) | live]
(push) ; 9
; [then-branch: 45 | k@115@16 >= i@96@16 + 1]
(assert (>= k@115@16 (+ i@96@16 1)))
; [eval] k <= j - 1
; [eval] j - 1
(pop) ; 9
(push) ; 9
; [else-branch: 45 | !(k@115@16 >= i@96@16 + 1)]
(assert (not (>= k@115@16 (+ i@96@16 1))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@115@16 (+ i@96@16 1))) (>= k@115@16 (+ i@96@16 1))))
(push) ; 8
; [then-branch: 46 | k@115@16 <= j@107@16 - 1 && k@115@16 >= i@96@16 + 1 | live]
; [else-branch: 46 | !(k@115@16 <= j@107@16 - 1 && k@115@16 >= i@96@16 + 1) | live]
(push) ; 9
; [then-branch: 46 | k@115@16 <= j@107@16 - 1 && k@115@16 >= i@96@16 + 1]
(assert (and (<= k@115@16 (- j@107@16 1)) (>= k@115@16 (+ i@96@16 1))))
; [eval] slot(a, k).val > pivot
; [eval] slot(a, k)
(push) ; 10
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k@115@16) (slot<Ref> a@6@16 j@57@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k@115@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k@115@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@102@16 (slot<Ref> a@6@16 k@115@16)))
        (pTaken@105@16 (slot<Ref> a@6@16 k@115@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k@115@16) (slot<Ref> a@6@16 i@96@16))
        $Perm.Write
        $Perm.No)
      (pTaken@104@16 (slot<Ref> a@6@16 k@115@16)))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(pop) ; 9
(push) ; 9
; [else-branch: 46 | !(k@115@16 <= j@107@16 - 1 && k@115@16 >= i@96@16 + 1)]
(assert (not (and (<= k@115@16 (- j@107@16 1)) (>= k@115@16 (+ i@96@16 1)))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or
  (not (and (<= k@115@16 (- j@107@16 1)) (>= k@115@16 (+ i@96@16 1))))
  (and (<= k@115@16 (- j@107@16 1)) (>= k@115@16 (+ i@96@16 1)))))
(pop) ; 7
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@115@16 Int)) (!
  (and
    (or (not (>= k@115@16 (+ i@96@16 1))) (>= k@115@16 (+ i@96@16 1)))
    (or
      (not (and (<= k@115@16 (- j@107@16 1)) (>= k@115@16 (+ i@96@16 1))))
      (and (<= k@115@16 (- j@107@16 1)) (>= k@115@16 (+ i@96@16 1)))))
  :pattern ((slot<Ref> a@6@16 k@115@16))
  :qid |prog.l55-aux|)))
(push) ; 7
(assert (not (forall ((k@115@16 Int)) (!
  (=>
    (and (<= k@115@16 (- j@107@16 1)) (>= k@115@16 (+ i@96@16 1)))
    (>
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k@115@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@115@16))
  :qid |prog.l55|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@115@16 Int)) (!
  (=>
    (and (<= k@115@16 (- j@107@16 1)) (>= k@115@16 (+ i@96@16 1)))
    (>
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k@115@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@115@16))
  :qid |prog.l55|)))
; [eval] (forall k$4: Int :: { slot(a, k$4) } 0 <= k$4 && k$4 <= lo - 1 ==> slot(a, k$4).val == old(slot(a, k$4).val))
(declare-const k$4@116@16 Int)
(push) ; 7
; [eval] 0 <= k$4 && k$4 <= lo - 1 ==> slot(a, k$4).val == old(slot(a, k$4).val)
; [eval] 0 <= k$4 && k$4 <= lo - 1
; [eval] 0 <= k$4
(push) ; 8
; [then-branch: 47 | 0 <= k$4@116@16 | live]
; [else-branch: 47 | !(0 <= k$4@116@16) | live]
(push) ; 9
; [then-branch: 47 | 0 <= k$4@116@16]
(assert (<= 0 k$4@116@16))
; [eval] k$4 <= lo - 1
; [eval] lo - 1
(pop) ; 9
(push) ; 9
; [else-branch: 47 | !(0 <= k$4@116@16)]
(assert (not (<= 0 k$4@116@16)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 k$4@116@16)) (<= 0 k$4@116@16)))
(push) ; 8
; [then-branch: 48 | k$4@116@16 <= lo@7@16 - 1 && 0 <= k$4@116@16 | live]
; [else-branch: 48 | !(k$4@116@16 <= lo@7@16 - 1 && 0 <= k$4@116@16) | live]
(push) ; 9
; [then-branch: 48 | k$4@116@16 <= lo@7@16 - 1 && 0 <= k$4@116@16]
(assert (and (<= k$4@116@16 (- lo@7@16 1)) (<= 0 k$4@116@16)))
; [eval] slot(a, k$4).val == old(slot(a, k$4).val)
; [eval] slot(a, k$4)
(push) ; 10
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k$4@116@16) (slot<Ref> a@6@16 j@57@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k$4@116@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$4@116@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@102@16 (slot<Ref> a@6@16 k$4@116@16)))
        (pTaken@105@16 (slot<Ref> a@6@16 k$4@116@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k$4@116@16) (slot<Ref> a@6@16 i@96@16))
        $Perm.Write
        $Perm.No)
      (pTaken@104@16 (slot<Ref> a@6@16 k$4@116@16)))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$4).val)
; [eval] slot(a, k$4)
(declare-const sm@117@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@117@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@117@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef54|)))
(declare-const pm@118@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@118@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@118@16  $FPM) r))
  :qid |qp.resPrmSumDef55|)))
(push) ; 10
(assert (not (< $Perm.No ($FVF.perm_val (as pm@118@16  $FPM) (slot<Ref> a@6@16 k$4@116@16)))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(pop) ; 9
(push) ; 9
; [else-branch: 48 | !(k$4@116@16 <= lo@7@16 - 1 && 0 <= k$4@116@16)]
(assert (not (and (<= k$4@116@16 (- lo@7@16 1)) (<= 0 k$4@116@16))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@117@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@117@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef54|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@118@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@118@16  $FPM) r))
  :qid |qp.resPrmSumDef55|)))
; Joined path conditions
(assert (or
  (not (and (<= k$4@116@16 (- lo@7@16 1)) (<= 0 k$4@116@16)))
  (and (<= k$4@116@16 (- lo@7@16 1)) (<= 0 k$4@116@16))))
(pop) ; 7
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@117@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@117@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef54|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@118@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@118@16  $FPM) r))
  :qid |qp.resPrmSumDef55|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$4@116@16 Int)) (!
  (and
    (or (not (<= 0 k$4@116@16)) (<= 0 k$4@116@16))
    (or
      (not (and (<= k$4@116@16 (- lo@7@16 1)) (<= 0 k$4@116@16)))
      (and (<= k$4@116@16 (- lo@7@16 1)) (<= 0 k$4@116@16))))
  :pattern ((slot<Ref> a@6@16 k$4@116@16))
  :qid |prog.l56-aux|)))
(push) ; 7
(assert (not (forall ((k$4@116@16 Int)) (!
  (=>
    (and (<= k$4@116@16 (- lo@7@16 1)) (<= 0 k$4@116@16))
    (=
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$4@116@16))
      ($FVF.lookup_val (as sm@117@16  $FVF<val>) (slot<Ref> a@6@16 k$4@116@16))))
  :pattern ((slot<Ref> a@6@16 k$4@116@16))
  :qid |prog.l56|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k$4@116@16 Int)) (!
  (=>
    (and (<= k$4@116@16 (- lo@7@16 1)) (<= 0 k$4@116@16))
    (=
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$4@116@16))
      ($FVF.lookup_val (as sm@117@16  $FVF<val>) (slot<Ref> a@6@16 k$4@116@16))))
  :pattern ((slot<Ref> a@6@16 k$4@116@16))
  :qid |prog.l56|)))
; [eval] (forall k$5: Int :: { slot(a, k$5) } hi + 1 <= k$5 && k$5 <= len(a) - 1 ==> slot(a, k$5).val == old(slot(a, k$5).val))
(declare-const k$5@119@16 Int)
(push) ; 7
; [eval] hi + 1 <= k$5 && k$5 <= len(a) - 1 ==> slot(a, k$5).val == old(slot(a, k$5).val)
; [eval] hi + 1 <= k$5 && k$5 <= len(a) - 1
; [eval] hi + 1 <= k$5
; [eval] hi + 1
(push) ; 8
; [then-branch: 49 | hi@8@16 + 1 <= k$5@119@16 | live]
; [else-branch: 49 | !(hi@8@16 + 1 <= k$5@119@16) | live]
(push) ; 9
; [then-branch: 49 | hi@8@16 + 1 <= k$5@119@16]
(assert (<= (+ hi@8@16 1) k$5@119@16))
; [eval] k$5 <= len(a) - 1
; [eval] len(a) - 1
; [eval] len(a)
(pop) ; 9
(push) ; 9
; [else-branch: 49 | !(hi@8@16 + 1 <= k$5@119@16)]
(assert (not (<= (+ hi@8@16 1) k$5@119@16)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (<= (+ hi@8@16 1) k$5@119@16)) (<= (+ hi@8@16 1) k$5@119@16)))
(push) ; 8
; [then-branch: 50 | k$5@119@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@119@16 | live]
; [else-branch: 50 | !(k$5@119@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@119@16) | live]
(push) ; 9
; [then-branch: 50 | k$5@119@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@119@16]
(assert (and (<= k$5@119@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@119@16)))
; [eval] slot(a, k$5).val == old(slot(a, k$5).val)
; [eval] slot(a, k$5)
(push) ; 10
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k$5@119@16) (slot<Ref> a@6@16 j@57@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k$5@119@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$5@119@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@102@16 (slot<Ref> a@6@16 k$5@119@16)))
        (pTaken@105@16 (slot<Ref> a@6@16 k$5@119@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k$5@119@16) (slot<Ref> a@6@16 i@96@16))
        $Perm.Write
        $Perm.No)
      (pTaken@104@16 (slot<Ref> a@6@16 k$5@119@16)))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$5).val)
; [eval] slot(a, k$5)
(declare-const sm@120@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@120@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@120@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef56|)))
(declare-const pm@121@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@121@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@121@16  $FPM) r))
  :qid |qp.resPrmSumDef57|)))
(push) ; 10
(assert (not (< $Perm.No ($FVF.perm_val (as pm@121@16  $FPM) (slot<Ref> a@6@16 k$5@119@16)))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(pop) ; 9
(push) ; 9
; [else-branch: 50 | !(k$5@119@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@119@16)]
(assert (not (and (<= k$5@119@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@119@16))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@120@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@120@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef56|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@121@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@121@16  $FPM) r))
  :qid |qp.resPrmSumDef57|)))
; Joined path conditions
(assert (or
  (not
    (and (<= k$5@119@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@119@16)))
  (and (<= k$5@119@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@119@16))))
(pop) ; 7
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@120@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@120@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef56|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@121@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@121@16  $FPM) r))
  :qid |qp.resPrmSumDef57|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$5@119@16 Int)) (!
  (and
    (or (not (<= (+ hi@8@16 1) k$5@119@16)) (<= (+ hi@8@16 1) k$5@119@16))
    (or
      (not
        (and
          (<= k$5@119@16 (- (len<Int> a@6@16) 1))
          (<= (+ hi@8@16 1) k$5@119@16)))
      (and (<= k$5@119@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@119@16))))
  :pattern ((slot<Ref> a@6@16 k$5@119@16))
  :qid |prog.l57-aux|)))
(push) ; 7
(assert (not (forall ((k$5@119@16 Int)) (!
  (=>
    (and (<= k$5@119@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@119@16))
    (=
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$5@119@16))
      ($FVF.lookup_val (as sm@120@16  $FVF<val>) (slot<Ref> a@6@16 k$5@119@16))))
  :pattern ((slot<Ref> a@6@16 k$5@119@16))
  :qid |prog.l57|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k$5@119@16 Int)) (!
  (=>
    (and (<= k$5@119@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@119@16))
    (=
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$5@119@16))
      ($FVF.lookup_val (as sm@120@16  $FVF<val>) (slot<Ref> a@6@16 k$5@119@16))))
  :pattern ((slot<Ref> a@6@16 k$5@119@16))
  :qid |prog.l57|)))
; [eval] (forall k$6: Int :: { slot(a, k$6) } lo <= k$6 && k$6 <= hi ==> lb <= slot(a, k$6).val && slot(a, k$6).val <= rb)
(declare-const k$6@122@16 Int)
(push) ; 7
; [eval] lo <= k$6 && k$6 <= hi ==> lb <= slot(a, k$6).val && slot(a, k$6).val <= rb
; [eval] lo <= k$6 && k$6 <= hi
; [eval] lo <= k$6
(push) ; 8
; [then-branch: 51 | lo@7@16 <= k$6@122@16 | live]
; [else-branch: 51 | !(lo@7@16 <= k$6@122@16) | live]
(push) ; 9
; [then-branch: 51 | lo@7@16 <= k$6@122@16]
(assert (<= lo@7@16 k$6@122@16))
; [eval] k$6 <= hi
(pop) ; 9
(push) ; 9
; [else-branch: 51 | !(lo@7@16 <= k$6@122@16)]
(assert (not (<= lo@7@16 k$6@122@16)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@7@16 k$6@122@16)) (<= lo@7@16 k$6@122@16)))
(push) ; 8
; [then-branch: 52 | k$6@122@16 <= hi@8@16 && lo@7@16 <= k$6@122@16 | live]
; [else-branch: 52 | !(k$6@122@16 <= hi@8@16 && lo@7@16 <= k$6@122@16) | live]
(push) ; 9
; [then-branch: 52 | k$6@122@16 <= hi@8@16 && lo@7@16 <= k$6@122@16]
(assert (and (<= k$6@122@16 hi@8@16) (<= lo@7@16 k$6@122@16)))
; [eval] lb <= slot(a, k$6).val && slot(a, k$6).val <= rb
; [eval] lb <= slot(a, k$6).val
; [eval] slot(a, k$6)
(push) ; 10
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k$6@122@16) (slot<Ref> a@6@16 j@57@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k$6@122@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$6@122@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@102@16 (slot<Ref> a@6@16 k$6@122@16)))
        (pTaken@105@16 (slot<Ref> a@6@16 k$6@122@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k$6@122@16) (slot<Ref> a@6@16 i@96@16))
        $Perm.Write
        $Perm.No)
      (pTaken@104@16 (slot<Ref> a@6@16 k$6@122@16)))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch: 53 | lb@9@16 <= Lookup(val,sm@113@16,slot[Ref](a@6@16, k$6@122@16)) | live]
; [else-branch: 53 | !(lb@9@16 <= Lookup(val,sm@113@16,slot[Ref](a@6@16, k$6@122@16))) | live]
(push) ; 11
; [then-branch: 53 | lb@9@16 <= Lookup(val,sm@113@16,slot[Ref](a@6@16, k$6@122@16))]
(assert (<=
  lb@9@16
  ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16))))
; [eval] slot(a, k$6).val <= rb
; [eval] slot(a, k$6)
(push) ; 12
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k$6@122@16) (slot<Ref> a@6@16 j@57@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k$6@122@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$6@122@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@102@16 (slot<Ref> a@6@16 k$6@122@16)))
        (pTaken@105@16 (slot<Ref> a@6@16 k$6@122@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k$6@122@16) (slot<Ref> a@6@16 i@96@16))
        $Perm.Write
        $Perm.No)
      (pTaken@104@16 (slot<Ref> a@6@16 k$6@122@16)))))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(pop) ; 11
(push) ; 11
; [else-branch: 53 | !(lb@9@16 <= Lookup(val,sm@113@16,slot[Ref](a@6@16, k$6@122@16)))]
(assert (not
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16)))))
(pop) ; 11
(pop) ; 10
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (<=
      lb@9@16
      ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16))))
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16)))))
(pop) ; 9
(push) ; 9
; [else-branch: 52 | !(k$6@122@16 <= hi@8@16 && lo@7@16 <= k$6@122@16)]
(assert (not (and (<= k$6@122@16 hi@8@16) (<= lo@7@16 k$6@122@16))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
(assert (=>
  (and (<= k$6@122@16 hi@8@16) (<= lo@7@16 k$6@122@16))
  (and
    (<= k$6@122@16 hi@8@16)
    (<= lo@7@16 k$6@122@16)
    (or
      (not
        (<=
          lb@9@16
          ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16))))
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16)))))))
; Joined path conditions
(assert (or
  (not (and (<= k$6@122@16 hi@8@16) (<= lo@7@16 k$6@122@16)))
  (and (<= k$6@122@16 hi@8@16) (<= lo@7@16 k$6@122@16))))
(pop) ; 7
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$6@122@16 Int)) (!
  (and
    (or (not (<= lo@7@16 k$6@122@16)) (<= lo@7@16 k$6@122@16))
    (=>
      (and (<= k$6@122@16 hi@8@16) (<= lo@7@16 k$6@122@16))
      (and
        (<= k$6@122@16 hi@8@16)
        (<= lo@7@16 k$6@122@16)
        (or
          (not
            (<=
              lb@9@16
              ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16))))
          (<=
            lb@9@16
            ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16))))))
    (or
      (not (and (<= k$6@122@16 hi@8@16) (<= lo@7@16 k$6@122@16)))
      (and (<= k$6@122@16 hi@8@16) (<= lo@7@16 k$6@122@16))))
  :pattern ((slot<Ref> a@6@16 k$6@122@16))
  :qid |prog.l58-aux|)))
(push) ; 7
(assert (not (forall ((k$6@122@16 Int)) (!
  (=>
    (and (<= k$6@122@16 hi@8@16) (<= lo@7@16 k$6@122@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16)))))
  :pattern ((slot<Ref> a@6@16 k$6@122@16))
  :qid |prog.l58|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k$6@122@16 Int)) (!
  (=>
    (and (<= k$6@122@16 hi@8@16) (<= lo@7@16 k$6@122@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@113@16  $FVF<val>) (slot<Ref> a@6@16 k$6@122@16)))))
  :pattern ((slot<Ref> a@6@16 k$6@122@16))
  :qid |prog.l58|)))
(pop) ; 6
(push) ; 6
; [else-branch: 41 | !(Lookup(val,sm@93@16,slot[Ref](a@6@16, j@57@16)) <= pivot@53@16)]
(assert (not
  (<=
    ($FVF.lookup_val (as sm@93@16  $FVF<val>) (slot<Ref> a@6@16 j@57@16))
    pivot@53@16)))
(pop) ; 6
; [eval] !(slot(a, j).val <= pivot)
; [eval] slot(a, j).val <= pivot
; [eval] slot(a, j)
(declare-const sm@123@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@123@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@123@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef58|)))
(declare-const pm@124@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@124@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@124@16  $FPM) r))
  :qid |qp.resPrmSumDef59|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@124@16  $FPM) (slot<Ref> a@6@16 j@57@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(set-option :timeout 10)
(assert (not (<=
  ($FVF.lookup_val (as sm@123@16  $FVF<val>) (slot<Ref> a@6@16 j@57@16))
  pivot@53@16)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 10)
(assert (not (not
  (<=
    ($FVF.lookup_val (as sm@123@16  $FVF<val>) (slot<Ref> a@6@16 j@57@16))
    pivot@53@16))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [then-branch: 54 | !(Lookup(val,sm@123@16,slot[Ref](a@6@16, j@57@16)) <= pivot@53@16) | live]
; [else-branch: 54 | Lookup(val,sm@123@16,slot[Ref](a@6@16, j@57@16)) <= pivot@53@16 | live]
(set-option :timeout 0)
(push) ; 6
; [then-branch: 54 | !(Lookup(val,sm@123@16,slot[Ref](a@6@16, j@57@16)) <= pivot@53@16)]
(assert (not
  (<=
    ($FVF.lookup_val (as sm@123@16  $FVF<val>) (slot<Ref> a@6@16 j@57@16))
    pivot@53@16)))
; [exec]
; j := j + 1
; [eval] j + 1
(declare-const j@125@16 Int)
(assert (= j@125@16 (+ j@57@16 1)))
; Loop head block: Re-establish invariant
(declare-const j$2@126@16 Int)
(push) ; 7
; [eval] 0 <= j$2 && j$2 < len(a)
; [eval] 0 <= j$2
(push) ; 8
; [then-branch: 55 | 0 <= j$2@126@16 | live]
; [else-branch: 55 | !(0 <= j$2@126@16) | live]
(push) ; 9
; [then-branch: 55 | 0 <= j$2@126@16]
(assert (<= 0 j$2@126@16))
; [eval] j$2 < len(a)
; [eval] len(a)
(pop) ; 9
(push) ; 9
; [else-branch: 55 | !(0 <= j$2@126@16)]
(assert (not (<= 0 j$2@126@16)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$2@126@16)) (<= 0 j$2@126@16)))
(assert (and (< j$2@126@16 (len<Int> a@6@16)) (<= 0 j$2@126@16)))
; [eval] slot(a, j$2)
(pop) ; 7
(declare-fun inv@127@16 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$2@126@16 Int)) (!
  (=>
    (and (< j$2@126@16 (len<Int> a@6@16)) (<= 0 j$2@126@16))
    (or (not (<= 0 j$2@126@16)) (<= 0 j$2@126@16)))
  :pattern ((slot<Ref> a@6@16 j$2@126@16))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 7
(assert (not (forall ((j$21@126@16 Int) (j$22@126@16 Int)) (!
  (=>
    (and
      (and (< j$21@126@16 (len<Int> a@6@16)) (<= 0 j$21@126@16))
      (and (< j$22@126@16 (len<Int> a@6@16)) (<= 0 j$22@126@16))
      (= (slot<Ref> a@6@16 j$21@126@16) (slot<Ref> a@6@16 j$22@126@16)))
    (= j$21@126@16 j$22@126@16))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$2@126@16 Int)) (!
  (=>
    (and (< j$2@126@16 (len<Int> a@6@16)) (<= 0 j$2@126@16))
    (= (inv@127@16 (slot<Ref> a@6@16 j$2@126@16)) j$2@126@16))
  :pattern ((slot<Ref> a@6@16 j$2@126@16))
  :qid |val-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@127@16 r) (len<Int> a@6@16)) (<= 0 (inv@127@16 r)))
    (= (slot<Ref> a@6@16 (inv@127@16 r)) r))
  :pattern ((inv@127@16 r))
  :qid |val-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@128@16 ((r $Ref)) $Perm
  (ite
    (and (< (inv@127@16 r) (len<Int> a@6@16)) (<= 0 (inv@127@16 r)))
    ($Perm.min
      (ite
        (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
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
(push) ; 7
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (ite
        (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
        $Perm.Write
        $Perm.No)
      (pTaken@128@16 r))
    $Perm.No)
  
  :qid |quant-u-48|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (and (< (inv@127@16 r) (len<Int> a@6@16)) (<= 0 (inv@127@16 r)))
    (= (- $Perm.Write (pTaken@128@16 r)) $Perm.No))
  
  :qid |quant-u-49|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@129@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@129@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@129@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef60|)))
; [eval] j >= lo
(set-option :timeout 0)
(push) ; 7
(assert (not (>= j@125@16 lo@7@16)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (>= j@125@16 lo@7@16))
; [eval] j <= hi
(push) ; 7
(assert (not (<= j@125@16 hi@8@16)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (<= j@125@16 hi@8@16))
; [eval] i >= lo - 1
; [eval] lo - 1
; [eval] i < j
(push) ; 7
(assert (not (< i@55@16 j@125@16)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< i@55@16 j@125@16))
; [eval] slot(a, hi).val == pivot
; [eval] slot(a, hi)
(push) ; 7
(assert (not (and
  (< (inv@60@16 (slot<Ref> a@6@16 hi@8@16)) (len<Int> a@6@16))
  (<= 0 (inv@60@16 (slot<Ref> a@6@16 hi@8@16))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (=
  ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 hi@8@16))
  pivot@53@16)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (=
  ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 hi@8@16))
  pivot@53@16))
; [eval] (forall k: Int :: { slot(a, k) } k >= lo && k <= i ==> slot(a, k).val <= pivot)
(declare-const k@130@16 Int)
(push) ; 7
; [eval] k >= lo && k <= i ==> slot(a, k).val <= pivot
; [eval] k >= lo && k <= i
; [eval] k >= lo
(push) ; 8
; [then-branch: 56 | k@130@16 >= lo@7@16 | live]
; [else-branch: 56 | !(k@130@16 >= lo@7@16) | live]
(push) ; 9
; [then-branch: 56 | k@130@16 >= lo@7@16]
(assert (>= k@130@16 lo@7@16))
; [eval] k <= i
(pop) ; 9
(push) ; 9
; [else-branch: 56 | !(k@130@16 >= lo@7@16)]
(assert (not (>= k@130@16 lo@7@16)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@130@16 lo@7@16)) (>= k@130@16 lo@7@16)))
(push) ; 8
; [then-branch: 57 | k@130@16 <= i@55@16 && k@130@16 >= lo@7@16 | live]
; [else-branch: 57 | !(k@130@16 <= i@55@16 && k@130@16 >= lo@7@16) | live]
(push) ; 9
; [then-branch: 57 | k@130@16 <= i@55@16 && k@130@16 >= lo@7@16]
(assert (and (<= k@130@16 i@55@16) (>= k@130@16 lo@7@16)))
; [eval] slot(a, k).val <= pivot
; [eval] slot(a, k)
(push) ; 10
(assert (not (and
  (< (inv@60@16 (slot<Ref> a@6@16 k@130@16)) (len<Int> a@6@16))
  (<= 0 (inv@60@16 (slot<Ref> a@6@16 k@130@16))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(pop) ; 9
(push) ; 9
; [else-branch: 57 | !(k@130@16 <= i@55@16 && k@130@16 >= lo@7@16)]
(assert (not (and (<= k@130@16 i@55@16) (>= k@130@16 lo@7@16))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or
  (not (and (<= k@130@16 i@55@16) (>= k@130@16 lo@7@16)))
  (and (<= k@130@16 i@55@16) (>= k@130@16 lo@7@16))))
(pop) ; 7
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@130@16 Int)) (!
  (and
    (or (not (>= k@130@16 lo@7@16)) (>= k@130@16 lo@7@16))
    (or
      (not (and (<= k@130@16 i@55@16) (>= k@130@16 lo@7@16)))
      (and (<= k@130@16 i@55@16) (>= k@130@16 lo@7@16))))
  :pattern ((slot<Ref> a@6@16 k@130@16))
  :qid |prog.l54-aux|)))
(push) ; 7
(assert (not (forall ((k@130@16 Int)) (!
  (=>
    (and (<= k@130@16 i@55@16) (>= k@130@16 lo@7@16))
    (<=
      ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k@130@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@130@16))
  :qid |prog.l54|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@130@16 Int)) (!
  (=>
    (and (<= k@130@16 i@55@16) (>= k@130@16 lo@7@16))
    (<=
      ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k@130@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@130@16))
  :qid |prog.l54|)))
; [eval] (forall k: Int :: { slot(a, k) } k >= i + 1 && k <= j - 1 ==> slot(a, k).val > pivot)
(declare-const k@131@16 Int)
(push) ; 7
; [eval] k >= i + 1 && k <= j - 1 ==> slot(a, k).val > pivot
; [eval] k >= i + 1 && k <= j - 1
; [eval] k >= i + 1
; [eval] i + 1
(push) ; 8
; [then-branch: 58 | k@131@16 >= i@55@16 + 1 | live]
; [else-branch: 58 | !(k@131@16 >= i@55@16 + 1) | live]
(push) ; 9
; [then-branch: 58 | k@131@16 >= i@55@16 + 1]
(assert (>= k@131@16 (+ i@55@16 1)))
; [eval] k <= j - 1
; [eval] j - 1
(pop) ; 9
(push) ; 9
; [else-branch: 58 | !(k@131@16 >= i@55@16 + 1)]
(assert (not (>= k@131@16 (+ i@55@16 1))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@131@16 (+ i@55@16 1))) (>= k@131@16 (+ i@55@16 1))))
(push) ; 8
; [then-branch: 59 | k@131@16 <= j@125@16 - 1 && k@131@16 >= i@55@16 + 1 | live]
; [else-branch: 59 | !(k@131@16 <= j@125@16 - 1 && k@131@16 >= i@55@16 + 1) | live]
(push) ; 9
; [then-branch: 59 | k@131@16 <= j@125@16 - 1 && k@131@16 >= i@55@16 + 1]
(assert (and (<= k@131@16 (- j@125@16 1)) (>= k@131@16 (+ i@55@16 1))))
; [eval] slot(a, k).val > pivot
; [eval] slot(a, k)
(push) ; 10
(assert (not (and
  (< (inv@60@16 (slot<Ref> a@6@16 k@131@16)) (len<Int> a@6@16))
  (<= 0 (inv@60@16 (slot<Ref> a@6@16 k@131@16))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(pop) ; 9
(push) ; 9
; [else-branch: 59 | !(k@131@16 <= j@125@16 - 1 && k@131@16 >= i@55@16 + 1)]
(assert (not (and (<= k@131@16 (- j@125@16 1)) (>= k@131@16 (+ i@55@16 1)))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or
  (not (and (<= k@131@16 (- j@125@16 1)) (>= k@131@16 (+ i@55@16 1))))
  (and (<= k@131@16 (- j@125@16 1)) (>= k@131@16 (+ i@55@16 1)))))
(pop) ; 7
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@131@16 Int)) (!
  (and
    (or (not (>= k@131@16 (+ i@55@16 1))) (>= k@131@16 (+ i@55@16 1)))
    (or
      (not (and (<= k@131@16 (- j@125@16 1)) (>= k@131@16 (+ i@55@16 1))))
      (and (<= k@131@16 (- j@125@16 1)) (>= k@131@16 (+ i@55@16 1)))))
  :pattern ((slot<Ref> a@6@16 k@131@16))
  :qid |prog.l55-aux|)))
(push) ; 7
(assert (not (forall ((k@131@16 Int)) (!
  (=>
    (and (<= k@131@16 (- j@125@16 1)) (>= k@131@16 (+ i@55@16 1)))
    (>
      ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k@131@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@131@16))
  :qid |prog.l55|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@131@16 Int)) (!
  (=>
    (and (<= k@131@16 (- j@125@16 1)) (>= k@131@16 (+ i@55@16 1)))
    (>
      ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k@131@16))
      pivot@53@16))
  :pattern ((slot<Ref> a@6@16 k@131@16))
  :qid |prog.l55|)))
; [eval] (forall k$4: Int :: { slot(a, k$4) } 0 <= k$4 && k$4 <= lo - 1 ==> slot(a, k$4).val == old(slot(a, k$4).val))
(declare-const k$4@132@16 Int)
(push) ; 7
; [eval] 0 <= k$4 && k$4 <= lo - 1 ==> slot(a, k$4).val == old(slot(a, k$4).val)
; [eval] 0 <= k$4 && k$4 <= lo - 1
; [eval] 0 <= k$4
(push) ; 8
; [then-branch: 60 | 0 <= k$4@132@16 | live]
; [else-branch: 60 | !(0 <= k$4@132@16) | live]
(push) ; 9
; [then-branch: 60 | 0 <= k$4@132@16]
(assert (<= 0 k$4@132@16))
; [eval] k$4 <= lo - 1
; [eval] lo - 1
(pop) ; 9
(push) ; 9
; [else-branch: 60 | !(0 <= k$4@132@16)]
(assert (not (<= 0 k$4@132@16)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 k$4@132@16)) (<= 0 k$4@132@16)))
(push) ; 8
; [then-branch: 61 | k$4@132@16 <= lo@7@16 - 1 && 0 <= k$4@132@16 | live]
; [else-branch: 61 | !(k$4@132@16 <= lo@7@16 - 1 && 0 <= k$4@132@16) | live]
(push) ; 9
; [then-branch: 61 | k$4@132@16 <= lo@7@16 - 1 && 0 <= k$4@132@16]
(assert (and (<= k$4@132@16 (- lo@7@16 1)) (<= 0 k$4@132@16)))
; [eval] slot(a, k$4).val == old(slot(a, k$4).val)
; [eval] slot(a, k$4)
(push) ; 10
(assert (not (and
  (< (inv@60@16 (slot<Ref> a@6@16 k$4@132@16)) (len<Int> a@6@16))
  (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$4@132@16))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$4).val)
; [eval] slot(a, k$4)
(declare-const sm@133@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@133@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@133@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef61|)))
(declare-const pm@134@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@134@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@134@16  $FPM) r))
  :qid |qp.resPrmSumDef62|)))
(push) ; 10
(assert (not (< $Perm.No ($FVF.perm_val (as pm@134@16  $FPM) (slot<Ref> a@6@16 k$4@132@16)))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(pop) ; 9
(push) ; 9
; [else-branch: 61 | !(k$4@132@16 <= lo@7@16 - 1 && 0 <= k$4@132@16)]
(assert (not (and (<= k$4@132@16 (- lo@7@16 1)) (<= 0 k$4@132@16))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@133@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@133@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef61|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@134@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@134@16  $FPM) r))
  :qid |qp.resPrmSumDef62|)))
; Joined path conditions
(assert (or
  (not (and (<= k$4@132@16 (- lo@7@16 1)) (<= 0 k$4@132@16)))
  (and (<= k$4@132@16 (- lo@7@16 1)) (<= 0 k$4@132@16))))
(pop) ; 7
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@133@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@133@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef61|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@134@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@134@16  $FPM) r))
  :qid |qp.resPrmSumDef62|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$4@132@16 Int)) (!
  (and
    (or (not (<= 0 k$4@132@16)) (<= 0 k$4@132@16))
    (or
      (not (and (<= k$4@132@16 (- lo@7@16 1)) (<= 0 k$4@132@16)))
      (and (<= k$4@132@16 (- lo@7@16 1)) (<= 0 k$4@132@16))))
  :pattern ((slot<Ref> a@6@16 k$4@132@16))
  :qid |prog.l56-aux|)))
(push) ; 7
(assert (not (forall ((k$4@132@16 Int)) (!
  (=>
    (and (<= k$4@132@16 (- lo@7@16 1)) (<= 0 k$4@132@16))
    (=
      ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$4@132@16))
      ($FVF.lookup_val (as sm@133@16  $FVF<val>) (slot<Ref> a@6@16 k$4@132@16))))
  :pattern ((slot<Ref> a@6@16 k$4@132@16))
  :qid |prog.l56|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k$4@132@16 Int)) (!
  (=>
    (and (<= k$4@132@16 (- lo@7@16 1)) (<= 0 k$4@132@16))
    (=
      ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$4@132@16))
      ($FVF.lookup_val (as sm@133@16  $FVF<val>) (slot<Ref> a@6@16 k$4@132@16))))
  :pattern ((slot<Ref> a@6@16 k$4@132@16))
  :qid |prog.l56|)))
; [eval] (forall k$5: Int :: { slot(a, k$5) } hi + 1 <= k$5 && k$5 <= len(a) - 1 ==> slot(a, k$5).val == old(slot(a, k$5).val))
(declare-const k$5@135@16 Int)
(push) ; 7
; [eval] hi + 1 <= k$5 && k$5 <= len(a) - 1 ==> slot(a, k$5).val == old(slot(a, k$5).val)
; [eval] hi + 1 <= k$5 && k$5 <= len(a) - 1
; [eval] hi + 1 <= k$5
; [eval] hi + 1
(push) ; 8
; [then-branch: 62 | hi@8@16 + 1 <= k$5@135@16 | live]
; [else-branch: 62 | !(hi@8@16 + 1 <= k$5@135@16) | live]
(push) ; 9
; [then-branch: 62 | hi@8@16 + 1 <= k$5@135@16]
(assert (<= (+ hi@8@16 1) k$5@135@16))
; [eval] k$5 <= len(a) - 1
; [eval] len(a) - 1
; [eval] len(a)
(pop) ; 9
(push) ; 9
; [else-branch: 62 | !(hi@8@16 + 1 <= k$5@135@16)]
(assert (not (<= (+ hi@8@16 1) k$5@135@16)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (<= (+ hi@8@16 1) k$5@135@16)) (<= (+ hi@8@16 1) k$5@135@16)))
(push) ; 8
; [then-branch: 63 | k$5@135@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@135@16 | live]
; [else-branch: 63 | !(k$5@135@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@135@16) | live]
(push) ; 9
; [then-branch: 63 | k$5@135@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@135@16]
(assert (and (<= k$5@135@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@135@16)))
; [eval] slot(a, k$5).val == old(slot(a, k$5).val)
; [eval] slot(a, k$5)
(push) ; 10
(assert (not (and
  (< (inv@60@16 (slot<Ref> a@6@16 k$5@135@16)) (len<Int> a@6@16))
  (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$5@135@16))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$5).val)
; [eval] slot(a, k$5)
(declare-const sm@136@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@136@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@136@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef63|)))
(declare-const pm@137@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@137@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@137@16  $FPM) r))
  :qid |qp.resPrmSumDef64|)))
(push) ; 10
(assert (not (< $Perm.No ($FVF.perm_val (as pm@137@16  $FPM) (slot<Ref> a@6@16 k$5@135@16)))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(pop) ; 9
(push) ; 9
; [else-branch: 63 | !(k$5@135@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$5@135@16)]
(assert (not (and (<= k$5@135@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@135@16))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@136@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@136@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef63|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@137@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@137@16  $FPM) r))
  :qid |qp.resPrmSumDef64|)))
; Joined path conditions
(assert (or
  (not
    (and (<= k$5@135@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@135@16)))
  (and (<= k$5@135@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@135@16))))
(pop) ; 7
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@136@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@136@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef63|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@137@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@137@16  $FPM) r))
  :qid |qp.resPrmSumDef64|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$5@135@16 Int)) (!
  (and
    (or (not (<= (+ hi@8@16 1) k$5@135@16)) (<= (+ hi@8@16 1) k$5@135@16))
    (or
      (not
        (and
          (<= k$5@135@16 (- (len<Int> a@6@16) 1))
          (<= (+ hi@8@16 1) k$5@135@16)))
      (and (<= k$5@135@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@135@16))))
  :pattern ((slot<Ref> a@6@16 k$5@135@16))
  :qid |prog.l57-aux|)))
(push) ; 7
(assert (not (forall ((k$5@135@16 Int)) (!
  (=>
    (and (<= k$5@135@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@135@16))
    (=
      ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$5@135@16))
      ($FVF.lookup_val (as sm@136@16  $FVF<val>) (slot<Ref> a@6@16 k$5@135@16))))
  :pattern ((slot<Ref> a@6@16 k$5@135@16))
  :qid |prog.l57|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k$5@135@16 Int)) (!
  (=>
    (and (<= k$5@135@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$5@135@16))
    (=
      ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$5@135@16))
      ($FVF.lookup_val (as sm@136@16  $FVF<val>) (slot<Ref> a@6@16 k$5@135@16))))
  :pattern ((slot<Ref> a@6@16 k$5@135@16))
  :qid |prog.l57|)))
; [eval] (forall k$6: Int :: { slot(a, k$6) } lo <= k$6 && k$6 <= hi ==> lb <= slot(a, k$6).val && slot(a, k$6).val <= rb)
(declare-const k$6@138@16 Int)
(push) ; 7
; [eval] lo <= k$6 && k$6 <= hi ==> lb <= slot(a, k$6).val && slot(a, k$6).val <= rb
; [eval] lo <= k$6 && k$6 <= hi
; [eval] lo <= k$6
(push) ; 8
; [then-branch: 64 | lo@7@16 <= k$6@138@16 | live]
; [else-branch: 64 | !(lo@7@16 <= k$6@138@16) | live]
(push) ; 9
; [then-branch: 64 | lo@7@16 <= k$6@138@16]
(assert (<= lo@7@16 k$6@138@16))
; [eval] k$6 <= hi
(pop) ; 9
(push) ; 9
; [else-branch: 64 | !(lo@7@16 <= k$6@138@16)]
(assert (not (<= lo@7@16 k$6@138@16)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@7@16 k$6@138@16)) (<= lo@7@16 k$6@138@16)))
(push) ; 8
; [then-branch: 65 | k$6@138@16 <= hi@8@16 && lo@7@16 <= k$6@138@16 | live]
; [else-branch: 65 | !(k$6@138@16 <= hi@8@16 && lo@7@16 <= k$6@138@16) | live]
(push) ; 9
; [then-branch: 65 | k$6@138@16 <= hi@8@16 && lo@7@16 <= k$6@138@16]
(assert (and (<= k$6@138@16 hi@8@16) (<= lo@7@16 k$6@138@16)))
; [eval] lb <= slot(a, k$6).val && slot(a, k$6).val <= rb
; [eval] lb <= slot(a, k$6).val
; [eval] slot(a, k$6)
(push) ; 10
(assert (not (and
  (< (inv@60@16 (slot<Ref> a@6@16 k$6@138@16)) (len<Int> a@6@16))
  (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$6@138@16))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch: 66 | lb@9@16 <= Lookup(val,sm@129@16,slot[Ref](a@6@16, k$6@138@16)) | live]
; [else-branch: 66 | !(lb@9@16 <= Lookup(val,sm@129@16,slot[Ref](a@6@16, k$6@138@16))) | live]
(push) ; 11
; [then-branch: 66 | lb@9@16 <= Lookup(val,sm@129@16,slot[Ref](a@6@16, k$6@138@16))]
(assert (<=
  lb@9@16
  ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16))))
; [eval] slot(a, k$6).val <= rb
; [eval] slot(a, k$6)
(push) ; 12
(assert (not (and
  (< (inv@60@16 (slot<Ref> a@6@16 k$6@138@16)) (len<Int> a@6@16))
  (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$6@138@16))))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(pop) ; 11
(push) ; 11
; [else-branch: 66 | !(lb@9@16 <= Lookup(val,sm@129@16,slot[Ref](a@6@16, k$6@138@16)))]
(assert (not
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16)))))
(pop) ; 11
(pop) ; 10
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (<=
      lb@9@16
      ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16))))
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16)))))
(pop) ; 9
(push) ; 9
; [else-branch: 65 | !(k$6@138@16 <= hi@8@16 && lo@7@16 <= k$6@138@16)]
(assert (not (and (<= k$6@138@16 hi@8@16) (<= lo@7@16 k$6@138@16))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
(assert (=>
  (and (<= k$6@138@16 hi@8@16) (<= lo@7@16 k$6@138@16))
  (and
    (<= k$6@138@16 hi@8@16)
    (<= lo@7@16 k$6@138@16)
    (or
      (not
        (<=
          lb@9@16
          ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16))))
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16)))))))
; Joined path conditions
(assert (or
  (not (and (<= k$6@138@16 hi@8@16) (<= lo@7@16 k$6@138@16)))
  (and (<= k$6@138@16 hi@8@16) (<= lo@7@16 k$6@138@16))))
(pop) ; 7
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$6@138@16 Int)) (!
  (and
    (or (not (<= lo@7@16 k$6@138@16)) (<= lo@7@16 k$6@138@16))
    (=>
      (and (<= k$6@138@16 hi@8@16) (<= lo@7@16 k$6@138@16))
      (and
        (<= k$6@138@16 hi@8@16)
        (<= lo@7@16 k$6@138@16)
        (or
          (not
            (<=
              lb@9@16
              ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16))))
          (<=
            lb@9@16
            ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16))))))
    (or
      (not (and (<= k$6@138@16 hi@8@16) (<= lo@7@16 k$6@138@16)))
      (and (<= k$6@138@16 hi@8@16) (<= lo@7@16 k$6@138@16))))
  :pattern ((slot<Ref> a@6@16 k$6@138@16))
  :qid |prog.l58-aux|)))
(push) ; 7
(assert (not (forall ((k$6@138@16 Int)) (!
  (=>
    (and (<= k$6@138@16 hi@8@16) (<= lo@7@16 k$6@138@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16)))))
  :pattern ((slot<Ref> a@6@16 k$6@138@16))
  :qid |prog.l58|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k$6@138@16 Int)) (!
  (=>
    (and (<= k$6@138@16 hi@8@16) (<= lo@7@16 k$6@138@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@129@16  $FVF<val>) (slot<Ref> a@6@16 k$6@138@16)))))
  :pattern ((slot<Ref> a@6@16 k$6@138@16))
  :qid |prog.l58|)))
(pop) ; 6
(push) ; 6
; [else-branch: 54 | Lookup(val,sm@123@16,slot[Ref](a@6@16, j@57@16)) <= pivot@53@16]
(assert (<=
  ($FVF.lookup_val (as sm@123@16  $FVF<val>) (slot<Ref> a@6@16 j@57@16))
  pivot@53@16))
(pop) ; 6
(pop) ; 5
(push) ; 5
; [else-branch: 40 | !(j@57@16 <= hi@8@16 - 1)]
(assert (not (<= j@57@16 (- hi@8@16 1))))
(pop) ; 5
; [eval] !(j <= hi - 1)
; [eval] j <= hi - 1
; [eval] hi - 1
(push) ; 5
(set-option :timeout 10)
(assert (not (<= j@57@16 (- hi@8@16 1))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (not (<= j@57@16 (- hi@8@16 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [then-branch: 67 | !(j@57@16 <= hi@8@16 - 1) | live]
; [else-branch: 67 | j@57@16 <= hi@8@16 - 1 | live]
(set-option :timeout 0)
(push) ; 5
; [then-branch: 67 | !(j@57@16 <= hi@8@16 - 1)]
(assert (not (<= j@57@16 (- hi@8@16 1))))
; [exec]
; i := i + 1
; [eval] i + 1
(declare-const i@139@16 Int)
(assert (= i@139@16 (+ i@55@16 1)))
; [exec]
; tmp2 := slot(a, i).val
; [eval] slot(a, i)
(declare-const sm@140@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@140@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@140@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef65|)))
(declare-const pm@141@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@141@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@141@16  $FPM) r))
  :qid |qp.resPrmSumDef66|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@141@16  $FPM) (slot<Ref> a@6@16 i@139@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const tmp2@142@16 Int)
(assert (=
  tmp2@142@16
  ($FVF.lookup_val (as sm@140@16  $FVF<val>) (slot<Ref> a@6@16 i@139@16))))
; [exec]
; slot(a, i).val := slot(a, hi).val
; [eval] slot(a, i)
; [eval] slot(a, hi)
(declare-const sm@143@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
    (=
      ($FVF.lookup_val (as sm@143@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@143@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef67|)))
(declare-const pm@144@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@144@16  $FPM) r)
    (ite
      (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@144@16  $FPM) r))
  :qid |qp.resPrmSumDef68|)))
(push) ; 6
(assert (not (< $Perm.No ($FVF.perm_val (as pm@144@16  $FPM) (slot<Ref> a@6@16 hi@8@16)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Precomputing data for removing quantified permissions
(define-fun pTaken@145@16 ((r $Ref)) $Perm
  (ite
    (= r (slot<Ref> a@6@16 i@139@16))
    ($Perm.min
      (ite
        (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
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
(push) ; 6
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (ite
        (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
        $Perm.Write
        $Perm.No)
      (pTaken@145@16 r))
    $Perm.No)
  
  :qid |quant-u-51|))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (= r (slot<Ref> a@6@16 i@139@16))
    (= (- $Perm.Write (pTaken@145@16 r)) $Perm.No))
  
  :qid |quant-u-52|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@146@16 $FVF<val>)
; Definitional axioms for singleton-FVF's value
(assert (=
  ($FVF.lookup_val (as sm@146@16  $FVF<val>) (slot<Ref> a@6@16 i@139@16))
  ($FVF.lookup_val (as sm@143@16  $FVF<val>) (slot<Ref> a@6@16 hi@8@16))))
; [exec]
; slot(a, hi).val := tmp2
; [eval] slot(a, hi)
; Precomputing data for removing quantified permissions
(define-fun pTaken@147@16 ((r $Ref)) $Perm
  (ite
    (= r (slot<Ref> a@6@16 hi@8@16))
    ($Perm.min
      (ite (= r (slot<Ref> a@6@16 i@139@16)) $Perm.Write $Perm.No)
      $Perm.Write)
    $Perm.No))
(define-fun pTaken@148@16 ((r $Ref)) $Perm
  (ite
    (= r (slot<Ref> a@6@16 hi@8@16))
    ($Perm.min
      (-
        (ite
          (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
          $Perm.Write
          $Perm.No)
        (pTaken@145@16 r))
      (- $Perm.Write (pTaken@147@16 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Chunk depleted?
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 500)
(assert (not (=
  (-
    (ite
      (= (slot<Ref> a@6@16 i@139@16) (slot<Ref> a@6@16 i@139@16))
      $Perm.Write
      $Perm.No)
    (pTaken@147@16 (slot<Ref> a@6@16 i@139@16)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (= r (slot<Ref> a@6@16 hi@8@16))
    (= (- $Perm.Write (pTaken@147@16 r)) $Perm.No))
  
  :qid |quant-u-55|))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (-
        (ite
          (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
          $Perm.Write
          $Perm.No)
        (pTaken@145@16 r))
      (pTaken@148@16 r))
    $Perm.No)
  
  :qid |quant-u-56|))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (= r (slot<Ref> a@6@16 hi@8@16))
    (= (- (- $Perm.Write (pTaken@147@16 r)) (pTaken@148@16 r)) $Perm.No))
  
  :qid |quant-u-57|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@149@16 $FVF<val>)
; Definitional axioms for singleton-FVF's value
(assert (=
  ($FVF.lookup_val (as sm@149@16  $FVF<val>) (slot<Ref> a@6@16 hi@8@16))
  tmp2@142@16))
(declare-const j$1@150@16 Int)
(set-option :timeout 0)
(push) ; 6
; [eval] 0 <= j$1 && j$1 < len(a)
; [eval] 0 <= j$1
(push) ; 7
; [then-branch: 68 | 0 <= j$1@150@16 | live]
; [else-branch: 68 | !(0 <= j$1@150@16) | live]
(push) ; 8
; [then-branch: 68 | 0 <= j$1@150@16]
(assert (<= 0 j$1@150@16))
; [eval] j$1 < len(a)
; [eval] len(a)
(pop) ; 8
(push) ; 8
; [else-branch: 68 | !(0 <= j$1@150@16)]
(assert (not (<= 0 j$1@150@16)))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 j$1@150@16)) (<= 0 j$1@150@16)))
(assert (and (< j$1@150@16 (len<Int> a@6@16)) (<= 0 j$1@150@16)))
; [eval] slot(a, j$1)
(pop) ; 6
(declare-fun inv@151@16 ($Ref) Int)
; Nested auxiliary terms: globals
; Nested auxiliary terms: non-globals
(assert (forall ((j$1@150@16 Int)) (!
  (=>
    (and (< j$1@150@16 (len<Int> a@6@16)) (<= 0 j$1@150@16))
    (or (not (<= 0 j$1@150@16)) (<= 0 j$1@150@16)))
  :pattern ((slot<Ref> a@6@16 j$1@150@16))
  :qid |val-aux|)))
; Check receiver injectivity
(push) ; 6
(assert (not (forall ((j$11@150@16 Int) (j$12@150@16 Int)) (!
  (=>
    (and
      (and (< j$11@150@16 (len<Int> a@6@16)) (<= 0 j$11@150@16))
      (and (< j$12@150@16 (len<Int> a@6@16)) (<= 0 j$12@150@16))
      (= (slot<Ref> a@6@16 j$11@150@16) (slot<Ref> a@6@16 j$12@150@16)))
    (= j$11@150@16 j$12@150@16))
  
  :qid |val-rcvrInj|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Definitional axioms for inverse functions
(assert (forall ((j$1@150@16 Int)) (!
  (=>
    (and (< j$1@150@16 (len<Int> a@6@16)) (<= 0 j$1@150@16))
    (= (inv@151@16 (slot<Ref> a@6@16 j$1@150@16)) j$1@150@16))
  :pattern ((slot<Ref> a@6@16 j$1@150@16))
  :qid |val-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@151@16 r) (len<Int> a@6@16)) (<= 0 (inv@151@16 r)))
    (= (slot<Ref> a@6@16 (inv@151@16 r)) r))
  :pattern ((inv@151@16 r))
  :qid |val-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@152@16 ((r $Ref)) $Perm
  (ite
    (and (< (inv@151@16 r) (len<Int> a@6@16)) (<= 0 (inv@151@16 r)))
    ($Perm.min
      (ite (= r (slot<Ref> a@6@16 hi@8@16)) $Perm.Write $Perm.No)
      $Perm.Write)
    $Perm.No))
(define-fun pTaken@153@16 ((r $Ref)) $Perm
  (ite
    (and (< (inv@151@16 r) (len<Int> a@6@16)) (<= 0 (inv@151@16 r)))
    ($Perm.min
      (-
        (-
          (ite
            (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
            $Perm.Write
            $Perm.No)
          (pTaken@145@16 r))
        (pTaken@148@16 r))
      (- $Perm.Write (pTaken@152@16 r)))
    $Perm.No))
(define-fun pTaken@154@16 ((r $Ref)) $Perm
  (ite
    (and (< (inv@151@16 r) (len<Int> a@6@16)) (<= 0 (inv@151@16 r)))
    ($Perm.min
      (-
        (ite (= r (slot<Ref> a@6@16 i@139@16)) $Perm.Write $Perm.No)
        (pTaken@147@16 r))
      (- (- $Perm.Write (pTaken@152@16 r)) (pTaken@153@16 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
(set-option :timeout 10)
(check-sat)
; unknown
; Chunk depleted?
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 500)
(assert (not (=
  (-
    (ite
      (= (slot<Ref> a@6@16 hi@8@16) (slot<Ref> a@6@16 hi@8@16))
      $Perm.Write
      $Perm.No)
    (pTaken@152@16 (slot<Ref> a@6@16 hi@8@16)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (and (< (inv@151@16 r) (len<Int> a@6@16)) (<= 0 (inv@151@16 r)))
    (= (- $Perm.Write (pTaken@152@16 r)) $Perm.No))
  
  :qid |quant-u-61|))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (-
        (-
          (ite
            (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
            $Perm.Write
            $Perm.No)
          (pTaken@145@16 r))
        (pTaken@148@16 r))
      (pTaken@153@16 r))
    $Perm.No)
  
  :qid |quant-u-62|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (and (< (inv@151@16 r) (len<Int> a@6@16)) (<= 0 (inv@151@16 r)))
    (= (- (- $Perm.Write (pTaken@152@16 r)) (pTaken@153@16 r)) $Perm.No))
  
  :qid |quant-u-63|))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 500)
(assert (not (=
  (-
    (-
      (ite
        (= (slot<Ref> a@6@16 i@139@16) (slot<Ref> a@6@16 i@139@16))
        $Perm.Write
        $Perm.No)
      (pTaken@147@16 (slot<Ref> a@6@16 i@139@16)))
    (pTaken@154@16 (slot<Ref> a@6@16 i@139@16)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Intermediate check if already taken enough permissions
(set-option :timeout 0)
(push) ; 6
(set-option :timeout 500)
(assert (not (forall ((r $Ref)) (!
  (=>
    (and (< (inv@151@16 r) (len<Int> a@6@16)) (<= 0 (inv@151@16 r)))
    (=
      (-
        (- (- $Perm.Write (pTaken@152@16 r)) (pTaken@153@16 r))
        (pTaken@154@16 r))
      $Perm.No))
  
  :qid |quant-u-65|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@155@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (= r (slot<Ref> a@6@16 hi@8@16))
    (=
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) r)
      ($FVF.lookup_val (as sm@149@16  $FVF<val>) r)))
  :pattern (($FVF.lookup_val (as sm@155@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val (as sm@149@16  $FVF<val>) r))
  :qid |qp.fvfValDef69|)))
(assert (forall ((r $Ref)) (!
  (=>
    (<
      $Perm.No
      (-
        (-
          (ite
            (and (< (inv@60@16 r) (len<Int> a@6@16)) (<= 0 (inv@60@16 r)))
            $Perm.Write
            $Perm.No)
          (pTaken@145@16 r))
        (pTaken@148@16 r)))
    (=
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r)))
  :pattern (($FVF.lookup_val (as sm@155@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@58@16)) r))
  :qid |qp.fvfValDef70|)))
(assert (forall ((r $Ref)) (!
  (=>
    (<
      $Perm.No
      (-
        (ite (= r (slot<Ref> a@6@16 i@139@16)) $Perm.Write $Perm.No)
        (pTaken@147@16 r)))
    (=
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) r)
      ($FVF.lookup_val (as sm@146@16  $FVF<val>) r)))
  :pattern (($FVF.lookup_val (as sm@155@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val (as sm@146@16  $FVF<val>) r))
  :qid |qp.fvfValDef71|)))
; [eval] i >= lo
(set-option :timeout 0)
(push) ; 6
(assert (not (>= i@139@16 lo@7@16)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (>= i@139@16 lo@7@16))
; [eval] i <= hi
(push) ; 6
(assert (not (<= i@139@16 hi@8@16)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (<= i@139@16 hi@8@16))
; [eval] (forall k: Int :: { slot(a, k) } k >= lo && k <= i ==> slot(a, k).val <= slot(a, i).val)
(declare-const k@156@16 Int)
(push) ; 6
; [eval] k >= lo && k <= i ==> slot(a, k).val <= slot(a, i).val
; [eval] k >= lo && k <= i
; [eval] k >= lo
(push) ; 7
; [then-branch: 69 | k@156@16 >= lo@7@16 | live]
; [else-branch: 69 | !(k@156@16 >= lo@7@16) | live]
(push) ; 8
; [then-branch: 69 | k@156@16 >= lo@7@16]
(assert (>= k@156@16 lo@7@16))
; [eval] k <= i
(pop) ; 8
(push) ; 8
; [else-branch: 69 | !(k@156@16 >= lo@7@16)]
(assert (not (>= k@156@16 lo@7@16)))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@156@16 lo@7@16)) (>= k@156@16 lo@7@16)))
(push) ; 7
; [then-branch: 70 | k@156@16 <= i@139@16 && k@156@16 >= lo@7@16 | live]
; [else-branch: 70 | !(k@156@16 <= i@139@16 && k@156@16 >= lo@7@16) | live]
(push) ; 8
; [then-branch: 70 | k@156@16 <= i@139@16 && k@156@16 >= lo@7@16]
(assert (and (<= k@156@16 i@139@16) (>= k@156@16 lo@7@16)))
; [eval] slot(a, k).val <= slot(a, i).val
; [eval] slot(a, k)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k@156@16) (slot<Ref> a@6@16 hi@8@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k@156@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k@156@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@145@16 (slot<Ref> a@6@16 k@156@16)))
        (pTaken@148@16 (slot<Ref> a@6@16 k@156@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k@156@16) (slot<Ref> a@6@16 i@139@16))
        $Perm.Write
        $Perm.No)
      (pTaken@147@16 (slot<Ref> a@6@16 k@156@16)))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [eval] slot(a, i)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 i@139@16) (slot<Ref> a@6@16 hi@8@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 i@139@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 i@139@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@145@16 (slot<Ref> a@6@16 i@139@16)))
        (pTaken@148@16 (slot<Ref> a@6@16 i@139@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 i@139@16) (slot<Ref> a@6@16 i@139@16))
        $Perm.Write
        $Perm.No)
      (pTaken@147@16 (slot<Ref> a@6@16 i@139@16)))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 70 | !(k@156@16 <= i@139@16 && k@156@16 >= lo@7@16)]
(assert (not (and (<= k@156@16 i@139@16) (>= k@156@16 lo@7@16))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or
  (not (and (<= k@156@16 i@139@16) (>= k@156@16 lo@7@16)))
  (and (<= k@156@16 i@139@16) (>= k@156@16 lo@7@16))))
(pop) ; 6
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@156@16 Int)) (!
  (and
    (or (not (>= k@156@16 lo@7@16)) (>= k@156@16 lo@7@16))
    (or
      (not (and (<= k@156@16 i@139@16) (>= k@156@16 lo@7@16)))
      (and (<= k@156@16 i@139@16) (>= k@156@16 lo@7@16))))
  :pattern ((slot<Ref> a@6@16 k@156@16))
  :qid |prog.l39-aux|)))
(push) ; 6
(assert (not (forall ((k@156@16 Int)) (!
  (=>
    (and (<= k@156@16 i@139@16) (>= k@156@16 lo@7@16))
    (<=
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k@156@16))
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 i@139@16))))
  :pattern ((slot<Ref> a@6@16 k@156@16))
  :qid |prog.l39|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@156@16 Int)) (!
  (=>
    (and (<= k@156@16 i@139@16) (>= k@156@16 lo@7@16))
    (<=
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k@156@16))
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 i@139@16))))
  :pattern ((slot<Ref> a@6@16 k@156@16))
  :qid |prog.l39|)))
; [eval] (forall k: Int :: { slot(a, k) } k >= i + 1 && k <= hi ==> slot(a, k).val > slot(a, i).val)
(declare-const k@157@16 Int)
(push) ; 6
; [eval] k >= i + 1 && k <= hi ==> slot(a, k).val > slot(a, i).val
; [eval] k >= i + 1 && k <= hi
; [eval] k >= i + 1
; [eval] i + 1
(push) ; 7
; [then-branch: 71 | k@157@16 >= i@139@16 + 1 | live]
; [else-branch: 71 | !(k@157@16 >= i@139@16 + 1) | live]
(push) ; 8
; [then-branch: 71 | k@157@16 >= i@139@16 + 1]
(assert (>= k@157@16 (+ i@139@16 1)))
; [eval] k <= hi
(pop) ; 8
(push) ; 8
; [else-branch: 71 | !(k@157@16 >= i@139@16 + 1)]
(assert (not (>= k@157@16 (+ i@139@16 1))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or (not (>= k@157@16 (+ i@139@16 1))) (>= k@157@16 (+ i@139@16 1))))
(push) ; 7
; [then-branch: 72 | k@157@16 <= hi@8@16 && k@157@16 >= i@139@16 + 1 | live]
; [else-branch: 72 | !(k@157@16 <= hi@8@16 && k@157@16 >= i@139@16 + 1) | live]
(push) ; 8
; [then-branch: 72 | k@157@16 <= hi@8@16 && k@157@16 >= i@139@16 + 1]
(assert (and (<= k@157@16 hi@8@16) (>= k@157@16 (+ i@139@16 1))))
; [eval] slot(a, k).val > slot(a, i).val
; [eval] slot(a, k)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k@157@16) (slot<Ref> a@6@16 hi@8@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k@157@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k@157@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@145@16 (slot<Ref> a@6@16 k@157@16)))
        (pTaken@148@16 (slot<Ref> a@6@16 k@157@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k@157@16) (slot<Ref> a@6@16 i@139@16))
        $Perm.Write
        $Perm.No)
      (pTaken@147@16 (slot<Ref> a@6@16 k@157@16)))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [eval] slot(a, i)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 i@139@16) (slot<Ref> a@6@16 hi@8@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 i@139@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 i@139@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@145@16 (slot<Ref> a@6@16 i@139@16)))
        (pTaken@148@16 (slot<Ref> a@6@16 i@139@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 i@139@16) (slot<Ref> a@6@16 i@139@16))
        $Perm.Write
        $Perm.No)
      (pTaken@147@16 (slot<Ref> a@6@16 i@139@16)))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 72 | !(k@157@16 <= hi@8@16 && k@157@16 >= i@139@16 + 1)]
(assert (not (and (<= k@157@16 hi@8@16) (>= k@157@16 (+ i@139@16 1)))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or
  (not (and (<= k@157@16 hi@8@16) (>= k@157@16 (+ i@139@16 1))))
  (and (<= k@157@16 hi@8@16) (>= k@157@16 (+ i@139@16 1)))))
(pop) ; 6
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k@157@16 Int)) (!
  (and
    (or (not (>= k@157@16 (+ i@139@16 1))) (>= k@157@16 (+ i@139@16 1)))
    (or
      (not (and (<= k@157@16 hi@8@16) (>= k@157@16 (+ i@139@16 1))))
      (and (<= k@157@16 hi@8@16) (>= k@157@16 (+ i@139@16 1)))))
  :pattern ((slot<Ref> a@6@16 k@157@16))
  :qid |prog.l40-aux|)))
(push) ; 6
(assert (not (forall ((k@157@16 Int)) (!
  (=>
    (and (<= k@157@16 hi@8@16) (>= k@157@16 (+ i@139@16 1)))
    (>
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k@157@16))
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 i@139@16))))
  :pattern ((slot<Ref> a@6@16 k@157@16))
  :qid |prog.l40|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@157@16 Int)) (!
  (=>
    (and (<= k@157@16 hi@8@16) (>= k@157@16 (+ i@139@16 1)))
    (>
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k@157@16))
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 i@139@16))))
  :pattern ((slot<Ref> a@6@16 k@157@16))
  :qid |prog.l40|)))
; [eval] (forall k$1: Int :: { slot(a, k$1) } 0 <= k$1 && k$1 <= lo - 1 ==> slot(a, k$1).val == old(slot(a, k$1).val))
(declare-const k$1@158@16 Int)
(push) ; 6
; [eval] 0 <= k$1 && k$1 <= lo - 1 ==> slot(a, k$1).val == old(slot(a, k$1).val)
; [eval] 0 <= k$1 && k$1 <= lo - 1
; [eval] 0 <= k$1
(push) ; 7
; [then-branch: 73 | 0 <= k$1@158@16 | live]
; [else-branch: 73 | !(0 <= k$1@158@16) | live]
(push) ; 8
; [then-branch: 73 | 0 <= k$1@158@16]
(assert (<= 0 k$1@158@16))
; [eval] k$1 <= lo - 1
; [eval] lo - 1
(pop) ; 8
(push) ; 8
; [else-branch: 73 | !(0 <= k$1@158@16)]
(assert (not (<= 0 k$1@158@16)))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or (not (<= 0 k$1@158@16)) (<= 0 k$1@158@16)))
(push) ; 7
; [then-branch: 74 | k$1@158@16 <= lo@7@16 - 1 && 0 <= k$1@158@16 | live]
; [else-branch: 74 | !(k$1@158@16 <= lo@7@16 - 1 && 0 <= k$1@158@16) | live]
(push) ; 8
; [then-branch: 74 | k$1@158@16 <= lo@7@16 - 1 && 0 <= k$1@158@16]
(assert (and (<= k$1@158@16 (- lo@7@16 1)) (<= 0 k$1@158@16)))
; [eval] slot(a, k$1).val == old(slot(a, k$1).val)
; [eval] slot(a, k$1)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k$1@158@16) (slot<Ref> a@6@16 hi@8@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k$1@158@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$1@158@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@145@16 (slot<Ref> a@6@16 k$1@158@16)))
        (pTaken@148@16 (slot<Ref> a@6@16 k$1@158@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k$1@158@16) (slot<Ref> a@6@16 i@139@16))
        $Perm.Write
        $Perm.No)
      (pTaken@147@16 (slot<Ref> a@6@16 k$1@158@16)))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$1).val)
; [eval] slot(a, k$1)
(declare-const sm@159@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@159@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@159@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef72|)))
(declare-const pm@160@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@160@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@160@16  $FPM) r))
  :qid |qp.resPrmSumDef73|)))
(push) ; 9
(assert (not (< $Perm.No ($FVF.perm_val (as pm@160@16  $FPM) (slot<Ref> a@6@16 k$1@158@16)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 74 | !(k$1@158@16 <= lo@7@16 - 1 && 0 <= k$1@158@16)]
(assert (not (and (<= k$1@158@16 (- lo@7@16 1)) (<= 0 k$1@158@16))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@159@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@159@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef72|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@160@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@160@16  $FPM) r))
  :qid |qp.resPrmSumDef73|)))
; Joined path conditions
(assert (or
  (not (and (<= k$1@158@16 (- lo@7@16 1)) (<= 0 k$1@158@16)))
  (and (<= k$1@158@16 (- lo@7@16 1)) (<= 0 k$1@158@16))))
(pop) ; 6
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@159@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@159@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef72|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@160@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@160@16  $FPM) r))
  :qid |qp.resPrmSumDef73|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$1@158@16 Int)) (!
  (and
    (or (not (<= 0 k$1@158@16)) (<= 0 k$1@158@16))
    (or
      (not (and (<= k$1@158@16 (- lo@7@16 1)) (<= 0 k$1@158@16)))
      (and (<= k$1@158@16 (- lo@7@16 1)) (<= 0 k$1@158@16))))
  :pattern ((slot<Ref> a@6@16 k$1@158@16))
  :qid |prog.l41-aux|)))
(push) ; 6
(assert (not (forall ((k$1@158@16 Int)) (!
  (=>
    (and (<= k$1@158@16 (- lo@7@16 1)) (<= 0 k$1@158@16))
    (=
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$1@158@16))
      ($FVF.lookup_val (as sm@159@16  $FVF<val>) (slot<Ref> a@6@16 k$1@158@16))))
  :pattern ((slot<Ref> a@6@16 k$1@158@16))
  :qid |prog.l41|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k$1@158@16 Int)) (!
  (=>
    (and (<= k$1@158@16 (- lo@7@16 1)) (<= 0 k$1@158@16))
    (=
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$1@158@16))
      ($FVF.lookup_val (as sm@159@16  $FVF<val>) (slot<Ref> a@6@16 k$1@158@16))))
  :pattern ((slot<Ref> a@6@16 k$1@158@16))
  :qid |prog.l41|)))
; [eval] (forall k$2: Int :: { slot(a, k$2) } hi + 1 <= k$2 && k$2 <= len(a) - 1 ==> slot(a, k$2).val == old(slot(a, k$2).val))
(declare-const k$2@161@16 Int)
(push) ; 6
; [eval] hi + 1 <= k$2 && k$2 <= len(a) - 1 ==> slot(a, k$2).val == old(slot(a, k$2).val)
; [eval] hi + 1 <= k$2 && k$2 <= len(a) - 1
; [eval] hi + 1 <= k$2
; [eval] hi + 1
(push) ; 7
; [then-branch: 75 | hi@8@16 + 1 <= k$2@161@16 | live]
; [else-branch: 75 | !(hi@8@16 + 1 <= k$2@161@16) | live]
(push) ; 8
; [then-branch: 75 | hi@8@16 + 1 <= k$2@161@16]
(assert (<= (+ hi@8@16 1) k$2@161@16))
; [eval] k$2 <= len(a) - 1
; [eval] len(a) - 1
; [eval] len(a)
(pop) ; 8
(push) ; 8
; [else-branch: 75 | !(hi@8@16 + 1 <= k$2@161@16)]
(assert (not (<= (+ hi@8@16 1) k$2@161@16)))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or (not (<= (+ hi@8@16 1) k$2@161@16)) (<= (+ hi@8@16 1) k$2@161@16)))
(push) ; 7
; [then-branch: 76 | k$2@161@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$2@161@16 | live]
; [else-branch: 76 | !(k$2@161@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$2@161@16) | live]
(push) ; 8
; [then-branch: 76 | k$2@161@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$2@161@16]
(assert (and (<= k$2@161@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@161@16)))
; [eval] slot(a, k$2).val == old(slot(a, k$2).val)
; [eval] slot(a, k$2)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k$2@161@16) (slot<Ref> a@6@16 hi@8@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k$2@161@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$2@161@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@145@16 (slot<Ref> a@6@16 k$2@161@16)))
        (pTaken@148@16 (slot<Ref> a@6@16 k$2@161@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k$2@161@16) (slot<Ref> a@6@16 i@139@16))
        $Perm.Write
        $Perm.No)
      (pTaken@147@16 (slot<Ref> a@6@16 k$2@161@16)))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [eval] old(slot(a, k$2).val)
; [eval] slot(a, k$2)
(declare-const sm@162@16 $FVF<val>)
; Definitional axioms for snapshot map values
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@162@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@162@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef74|)))
(declare-const pm@163@16 $FPM)
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@163@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@163@16  $FPM) r))
  :qid |qp.resPrmSumDef75|)))
(push) ; 9
(assert (not (< $Perm.No ($FVF.perm_val (as pm@163@16  $FPM) (slot<Ref> a@6@16 k$2@161@16)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(pop) ; 8
(push) ; 8
; [else-branch: 76 | !(k$2@161@16 <= len[Int](a@6@16) - 1 && hi@8@16 + 1 <= k$2@161@16)]
(assert (not (and (<= k$2@161@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@161@16))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@162@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@162@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef74|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@163@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@163@16  $FPM) r))
  :qid |qp.resPrmSumDef75|)))
; Joined path conditions
(assert (or
  (not
    (and (<= k$2@161@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@161@16)))
  (and (<= k$2@161@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@161@16))))
(pop) ; 6
; Nested auxiliary terms: globals (aux)
(assert (forall ((r $Ref)) (!
  (=>
    (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
    (=
      ($FVF.lookup_val (as sm@162@16  $FVF<val>) r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r)))
  :pattern (($FVF.lookup_val (as sm@162@16  $FVF<val>) r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<val> ($Snap.first $t@12@16)) r))
  :qid |qp.fvfValDef74|)))
(assert (forall ((r $Ref)) (!
  (=
    ($FVF.perm_val (as pm@163@16  $FPM) r)
    (ite
      (and (< (inv@14@16 r) (len<Int> a@6@16)) (<= 0 (inv@14@16 r)))
      $Perm.Write
      $Perm.No))
  :pattern (($FVF.perm_val (as pm@163@16  $FPM) r))
  :qid |qp.resPrmSumDef75|)))
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$2@161@16 Int)) (!
  (and
    (or (not (<= (+ hi@8@16 1) k$2@161@16)) (<= (+ hi@8@16 1) k$2@161@16))
    (or
      (not
        (and
          (<= k$2@161@16 (- (len<Int> a@6@16) 1))
          (<= (+ hi@8@16 1) k$2@161@16)))
      (and (<= k$2@161@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@161@16))))
  :pattern ((slot<Ref> a@6@16 k$2@161@16))
  :qid |prog.l42-aux|)))
(push) ; 6
(assert (not (forall ((k$2@161@16 Int)) (!
  (=>
    (and (<= k$2@161@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@161@16))
    (=
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$2@161@16))
      ($FVF.lookup_val (as sm@162@16  $FVF<val>) (slot<Ref> a@6@16 k$2@161@16))))
  :pattern ((slot<Ref> a@6@16 k$2@161@16))
  :qid |prog.l42|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k$2@161@16 Int)) (!
  (=>
    (and (<= k$2@161@16 (- (len<Int> a@6@16) 1)) (<= (+ hi@8@16 1) k$2@161@16))
    (=
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$2@161@16))
      ($FVF.lookup_val (as sm@162@16  $FVF<val>) (slot<Ref> a@6@16 k$2@161@16))))
  :pattern ((slot<Ref> a@6@16 k$2@161@16))
  :qid |prog.l42|)))
; [eval] (forall k$3: Int :: { slot(a, k$3) } lo <= k$3 && k$3 <= hi ==> lb <= slot(a, k$3).val && slot(a, k$3).val <= rb)
(declare-const k$3@164@16 Int)
(push) ; 6
; [eval] lo <= k$3 && k$3 <= hi ==> lb <= slot(a, k$3).val && slot(a, k$3).val <= rb
; [eval] lo <= k$3 && k$3 <= hi
; [eval] lo <= k$3
(push) ; 7
; [then-branch: 77 | lo@7@16 <= k$3@164@16 | live]
; [else-branch: 77 | !(lo@7@16 <= k$3@164@16) | live]
(push) ; 8
; [then-branch: 77 | lo@7@16 <= k$3@164@16]
(assert (<= lo@7@16 k$3@164@16))
; [eval] k$3 <= hi
(pop) ; 8
(push) ; 8
; [else-branch: 77 | !(lo@7@16 <= k$3@164@16)]
(assert (not (<= lo@7@16 k$3@164@16)))
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Joined path conditions
(assert (or (not (<= lo@7@16 k$3@164@16)) (<= lo@7@16 k$3@164@16)))
(push) ; 7
; [then-branch: 78 | k$3@164@16 <= hi@8@16 && lo@7@16 <= k$3@164@16 | live]
; [else-branch: 78 | !(k$3@164@16 <= hi@8@16 && lo@7@16 <= k$3@164@16) | live]
(push) ; 8
; [then-branch: 78 | k$3@164@16 <= hi@8@16 && lo@7@16 <= k$3@164@16]
(assert (and (<= k$3@164@16 hi@8@16) (<= lo@7@16 k$3@164@16)))
; [eval] lb <= slot(a, k$3).val && slot(a, k$3).val <= rb
; [eval] lb <= slot(a, k$3).val
; [eval] slot(a, k$3)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k$3@164@16) (slot<Ref> a@6@16 hi@8@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k$3@164@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$3@164@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@145@16 (slot<Ref> a@6@16 k$3@164@16)))
        (pTaken@148@16 (slot<Ref> a@6@16 k$3@164@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k$3@164@16) (slot<Ref> a@6@16 i@139@16))
        $Perm.Write
        $Perm.No)
      (pTaken@147@16 (slot<Ref> a@6@16 k$3@164@16)))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch: 79 | lb@9@16 <= Lookup(val,sm@155@16,slot[Ref](a@6@16, k$3@164@16)) | live]
; [else-branch: 79 | !(lb@9@16 <= Lookup(val,sm@155@16,slot[Ref](a@6@16, k$3@164@16))) | live]
(push) ; 10
; [then-branch: 79 | lb@9@16 <= Lookup(val,sm@155@16,slot[Ref](a@6@16, k$3@164@16))]
(assert (<=
  lb@9@16
  ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16))))
; [eval] slot(a, k$3).val <= rb
; [eval] slot(a, k$3)
(push) ; 11
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (= (slot<Ref> a@6@16 k$3@164@16) (slot<Ref> a@6@16 hi@8@16))
        $Perm.Write
        $Perm.No)
      (-
        (-
          (ite
            (and
              (< (inv@60@16 (slot<Ref> a@6@16 k$3@164@16)) (len<Int> a@6@16))
              (<= 0 (inv@60@16 (slot<Ref> a@6@16 k$3@164@16))))
            $Perm.Write
            $Perm.No)
          (pTaken@145@16 (slot<Ref> a@6@16 k$3@164@16)))
        (pTaken@148@16 (slot<Ref> a@6@16 k$3@164@16))))
    (-
      (ite
        (= (slot<Ref> a@6@16 k$3@164@16) (slot<Ref> a@6@16 i@139@16))
        $Perm.Write
        $Perm.No)
      (pTaken@147@16 (slot<Ref> a@6@16 k$3@164@16)))))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(pop) ; 10
(push) ; 10
; [else-branch: 79 | !(lb@9@16 <= Lookup(val,sm@155@16,slot[Ref](a@6@16, k$3@164@16)))]
(assert (not
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16)))))
(pop) ; 10
(pop) ; 9
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (<=
      lb@9@16
      ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16))))
  (<=
    lb@9@16
    ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16)))))
(pop) ; 8
(push) ; 8
; [else-branch: 78 | !(k$3@164@16 <= hi@8@16 && lo@7@16 <= k$3@164@16)]
(assert (not (and (<= k$3@164@16 hi@8@16) (<= lo@7@16 k$3@164@16))))
(pop) ; 8
(pop) ; 7
; Joined path conditions
(assert (=>
  (and (<= k$3@164@16 hi@8@16) (<= lo@7@16 k$3@164@16))
  (and
    (<= k$3@164@16 hi@8@16)
    (<= lo@7@16 k$3@164@16)
    (or
      (not
        (<=
          lb@9@16
          ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16))))
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16)))))))
; Joined path conditions
(assert (or
  (not (and (<= k$3@164@16 hi@8@16) (<= lo@7@16 k$3@164@16)))
  (and (<= k$3@164@16 hi@8@16) (<= lo@7@16 k$3@164@16))))
(pop) ; 6
; Nested auxiliary terms: globals (aux)
; Nested auxiliary terms: non-globals (aux)
(assert (forall ((k$3@164@16 Int)) (!
  (and
    (or (not (<= lo@7@16 k$3@164@16)) (<= lo@7@16 k$3@164@16))
    (=>
      (and (<= k$3@164@16 hi@8@16) (<= lo@7@16 k$3@164@16))
      (and
        (<= k$3@164@16 hi@8@16)
        (<= lo@7@16 k$3@164@16)
        (or
          (not
            (<=
              lb@9@16
              ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16))))
          (<=
            lb@9@16
            ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16))))))
    (or
      (not (and (<= k$3@164@16 hi@8@16) (<= lo@7@16 k$3@164@16)))
      (and (<= k$3@164@16 hi@8@16) (<= lo@7@16 k$3@164@16))))
  :pattern ((slot<Ref> a@6@16 k$3@164@16))
  :qid |prog.l43-aux|)))
(push) ; 6
(assert (not (forall ((k$3@164@16 Int)) (!
  (=>
    (and (<= k$3@164@16 hi@8@16) (<= lo@7@16 k$3@164@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16)))))
  :pattern ((slot<Ref> a@6@16 k$3@164@16))
  :qid |prog.l43|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k$3@164@16 Int)) (!
  (=>
    (and (<= k$3@164@16 hi@8@16) (<= lo@7@16 k$3@164@16))
    (and
      (<=
        ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16))
        rb@10@16)
      (<=
        lb@9@16
        ($FVF.lookup_val (as sm@155@16  $FVF<val>) (slot<Ref> a@6@16 k$3@164@16)))))
  :pattern ((slot<Ref> a@6@16 k$3@164@16))
  :qid |prog.l43|)))
(pop) ; 5
(push) ; 5
; [else-branch: 67 | j@57@16 <= hi@8@16 - 1]
(assert (<= j@57@16 (- hi@8@16 1)))
(pop) ; 5
(pop) ; 4
(pop) ; 3
(pop) ; 2
(pop) ; 1
