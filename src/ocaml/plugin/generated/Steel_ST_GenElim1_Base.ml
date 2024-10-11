open Prims
let (is_fvar : FStarC_Reflection_Types.term -> Prims.string -> Prims.bool) =
  FStar_Reflection_V1_Derived.is_fvar
let (is_any_fvar :
  FStarC_Reflection_Types.term -> Prims.string Prims.list -> Prims.bool) =
  FStar_Reflection_V1_Derived.is_any_fvar
let (is_squash :
  FStarC_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ -> is_any_fvar t ["Prims.squash"; "Prims.auto_squash"])))
      uu___
let (is_star_or_vstar :
  FStarC_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               is_any_fvar t
                 ["Steel.Effect.Common.star"; "Steel.Effect.Common.VStar"])))
      uu___
let rec (term_has_head :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun head ->
      let uu___ = FStar_Tactics_V1_SyntaxHelpers.collect_app t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (341)) (Prims.of_int (17))
                 (Prims.of_int (341)) (Prims.of_int (32)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (341)) Prims.int_one (Prims.of_int (352))
                 (Prims.of_int (12))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (hd, tl) ->
                  let uu___2 = FStarC_Tactics_V1_Builtins.term_eq_old hd head in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Steel.ST.GenElim1.Base.fsti"
                                (Prims.of_int (342)) (Prims.of_int (5))
                                (Prims.of_int (342)) (Prims.of_int (28)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Steel.ST.GenElim1.Base.fsti"
                                (Prims.of_int (342)) (Prims.of_int (2))
                                (Prims.of_int (352)) (Prims.of_int (12)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             if uu___3
                             then
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 -> true)))
                             else
                               Obj.magic
                                 (Obj.repr
                                    (let uu___5 = is_star_or_vstar hd in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (344))
                                                (Prims.of_int (10))
                                                (Prims.of_int (344))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (344))
                                                (Prims.of_int (7))
                                                (Prims.of_int (352))
                                                (Prims.of_int (12)))))
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun uu___6 ->
                                             if uu___6
                                             then
                                               Obj.magic
                                                 (Obj.repr
                                                    (match tl with
                                                     | (tg,
                                                        FStarC_Reflection_V1_Data.Q_Explicit)::
                                                         (td,
                                                          FStarC_Reflection_V1_Data.Q_Explicit)::[]
                                                         ->
                                                         Obj.repr
                                                           (let uu___7 =
                                                              term_has_head
                                                                tg head in
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (30)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (32)))))
                                                              (Obj.magic
                                                                 uu___7)
                                                              (fun uu___8 ->
                                                                 (fun uu___8
                                                                    ->
                                                                    if uu___8
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    true)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (term_has_head
                                                                    td head)))
                                                                   uu___8))
                                                     | uu___7 ->
                                                         Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___8 ->
                                                                 false))))
                                             else
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___8 -> false))))
                                            uu___6)))) uu___3))) uu___1)
let rec (solve_gen_unit_elim :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tl' ->
    let uu___ =
      let uu___1 =
        term_has_head tl'
          (FStarC_Reflection_V2_Builtins.pack_ln
             (FStarC_Reflection_V2_Data.Tv_FVar
                (FStarC_Reflection_V2_Builtins.pack_fv
                   ["Steel"; "ST"; "Util"; "pure"]))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (358)) (Prims.of_int (13))
                 (Prims.of_int (358)) (Prims.of_int (40)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (358)) (Prims.of_int (9)) (Prims.of_int (358))
                 (Prims.of_int (40))))) (Obj.magic uu___1)
        (fun uu___2 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___3 -> Prims.op_Negation uu___2)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (358)) (Prims.of_int (9)) (Prims.of_int (358))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (358)) (Prims.of_int (6)) (Prims.of_int (372))
               (Prims.of_int (47))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 ->
                         FStar_Reflection_V1_Derived.mk_app
                           (FStarC_Reflection_V2_Builtins.pack_ln
                              (FStarC_Reflection_V2_Data.Tv_FVar
                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                    ["Steel";
                                    "ST";
                                    "GenElim1";
                                    "Base";
                                    "GUEId"])))
                           [(tl', FStarC_Reflection_V1_Data.Q_Explicit)])))
            else
              Obj.magic
                (Obj.repr
                   (let uu___3 =
                      FStar_Tactics_V1_SyntaxHelpers.collect_app tl' in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim1.Base.fsti"
                               (Prims.of_int (361)) (Prims.of_int (23))
                               (Prims.of_int (361)) (Prims.of_int (40)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim1.Base.fsti"
                               (Prims.of_int (360)) (Prims.of_int (10))
                               (Prims.of_int (372)) (Prims.of_int (47)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         (fun uu___4 ->
                            match uu___4 with
                            | (hd, tl) ->
                                if is_fvar hd "Steel.ST.Util.pure"
                                then
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___5 ->
                                             FStar_Reflection_V1_Derived.mk_app
                                               (FStarC_Reflection_V2_Builtins.pack_ln
                                                  (FStarC_Reflection_V2_Data.Tv_FVar
                                                     (FStarC_Reflection_V2_Builtins.pack_fv
                                                        ["Steel";
                                                        "ST";
                                                        "GenElim1";
                                                        "Base";
                                                        "GUEPure"]))) tl)))
                                else
                                  Obj.magic
                                    (Obj.repr
                                       (let uu___6 = is_star_or_vstar hd in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Steel.ST.GenElim1.Base.fsti"
                                                   (Prims.of_int (364))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (364))
                                                   (Prims.of_int (35)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Steel.ST.GenElim1.Base.fsti"
                                                   (Prims.of_int (364))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (372))
                                                   (Prims.of_int (47)))))
                                          (Obj.magic uu___6)
                                          (fun uu___7 ->
                                             (fun uu___7 ->
                                                if uu___7
                                                then
                                                  Obj.magic
                                                    (Obj.repr
                                                       (match tl with
                                                        | (t1,
                                                           FStarC_Reflection_V1_Data.Q_Explicit)::
                                                            (t2,
                                                             FStarC_Reflection_V1_Data.Q_Explicit)::[]
                                                            ->
                                                            Obj.repr
                                                              (let uu___8 =
                                                                 solve_gen_unit_elim
                                                                   t1 in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (42)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (68)))))
                                                                 (Obj.magic
                                                                    uu___8)
                                                                 (fun uu___9
                                                                    ->
                                                                    (fun t1'
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    solve_gen_unit_elim
                                                                    t2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (68)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun t2'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GUEStar"])))
                                                                    [
                                                                    (t1',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (t2',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)]))))
                                                                    uu___9))
                                                        | uu___8 ->
                                                            Obj.repr
                                                              (FStar_Tactics_V1_Derived.fail
                                                                 "ill-formed star")))
                                                else
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___9 ->
                                                             FStar_Reflection_V1_Derived.mk_app
                                                               (FStarC_Reflection_V2_Builtins.pack_ln
                                                                  (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GUEId"])))
                                                               [(tl',
                                                                  FStarC_Reflection_V1_Data.Q_Explicit)]))))
                                               uu___7)))) uu___4)))) uu___1)
let (abstr_has_exists :
  FStarC_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (377)) (Prims.of_int (8)) (Prims.of_int (377))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (377)) (Prims.of_int (2)) (Prims.of_int (379))
               (Prims.of_int (14))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStarC_Reflection_V1_Data.Tv_Abs (uu___2, body) ->
                Obj.magic
                  (Obj.repr
                     (term_has_head body
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["Steel"; "ST"; "Util"; "exists_"])))))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> false))))
           uu___1)
let rec (get_universe :
  FStarC_Reflection_Types.universe ->
    (Prims.nat, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun u ->
       match FStarC_Reflection_V1_Builtins.inspect_universe u with
       | FStarC_Reflection_V1_Data.Uv_Zero ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Prims.int_zero)))
       | FStarC_Reflection_V1_Data.Uv_Succ u1 ->
           Obj.magic
             (Obj.repr
                (let uu___ = get_universe u1 in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                            (Prims.of_int (386)) (Prims.of_int (23))
                            (Prims.of_int (386)) (Prims.of_int (37)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                            (Prims.of_int (386)) (Prims.of_int (19))
                            (Prims.of_int (386)) (Prims.of_int (37)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.int_one + uu___1))))
       | uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_V1_Derived.fail
                   "get_universe: not an universe instantiation"))) uu___
let rec (solve_gen_elim :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tl' ->
    let uu___ =
      let uu___1 =
        term_has_head tl'
          (FStarC_Reflection_V2_Builtins.pack_ln
             (FStarC_Reflection_V2_Data.Tv_FVar
                (FStarC_Reflection_V2_Builtins.pack_fv
                   ["Steel"; "ST"; "Util"; "exists_"]))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (393)) (Prims.of_int (13))
                 (Prims.of_int (393)) (Prims.of_int (43)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (393)) (Prims.of_int (9)) (Prims.of_int (393))
                 (Prims.of_int (43))))) (Obj.magic uu___1)
        (fun uu___2 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___3 -> Prims.op_Negation uu___2)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (393)) (Prims.of_int (9)) (Prims.of_int (393))
               (Prims.of_int (43)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (393)) (Prims.of_int (6)) (Prims.of_int (458))
               (Prims.of_int (68))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then
              let uu___2 = solve_gen_unit_elim tl' in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                            (Prims.of_int (395)) (Prims.of_int (17))
                            (Prims.of_int (395)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                            (Prims.of_int (396)) (Prims.of_int (8))
                            (Prims.of_int (396)) (Prims.of_int (45)))))
                   (Obj.magic uu___2)
                   (fun t' ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           FStar_Reflection_V1_Derived.mk_app
                             (FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_FVar
                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                      ["Steel";
                                      "ST";
                                      "GenElim1";
                                      "Base";
                                      "GEUnit"])))
                             [(t', FStarC_Reflection_V1_Data.Q_Explicit)])))
            else
              (let uu___3 = FStar_Tactics_V1_SyntaxHelpers.collect_app tl' in
               Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                             (Prims.of_int (398)) (Prims.of_int (26))
                             (Prims.of_int (398)) (Prims.of_int (43)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                             (Prims.of_int (397)) (Prims.of_int (14))
                             (Prims.of_int (458)) (Prims.of_int (68)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       (fun uu___4 ->
                          match uu___4 with
                          | (hd, lbody) ->
                              if is_fvar hd "Steel.ST.Util.exists_"
                              then
                                let uu___5 =
                                  match FStar_Reflection_V1_Derived.inspect_ln_unascribe
                                          hd
                                  with
                                  | FStarC_Reflection_V1_Data.Tv_UInst
                                      (uu___6, u::uu___7) ->
                                      Obj.magic (Obj.repr (get_universe u))
                                  | uu___6 ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_V1_Derived.fail
                                              "ill-formed exists_: no universe found")) in
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Steel.ST.GenElim1.Base.fsti"
                                              (Prims.of_int (401))
                                              (Prims.of_int (25))
                                              (Prims.of_int (403))
                                              (Prims.of_int (63)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Steel.ST.GenElim1.Base.fsti"
                                              (Prims.of_int (404))
                                              (Prims.of_int (12))
                                              (Prims.of_int (437))
                                              (Prims.of_int (13)))))
                                     (Obj.magic uu___5)
                                     (fun uu___6 ->
                                        (fun universe ->
                                           let uu___6 =
                                             match lbody with
                                             | (ty,
                                                FStarC_Reflection_V1_Data.Q_Implicit)::
                                                 (body,
                                                  FStarC_Reflection_V1_Data.Q_Explicit)::[]
                                                 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___7 ->
                                                         ([(ty,
                                                             FStarC_Reflection_V1_Data.Q_Implicit)],
                                                           body)))
                                             | (body,
                                                FStarC_Reflection_V1_Data.Q_Explicit)::[]
                                                 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___7 ->
                                                         ([], body)))
                                             | uu___7 ->
                                                 Obj.magic
                                                   (FStar_Tactics_V1_Derived.fail
                                                      "ill-formed exists_") in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Steel.ST.GenElim1.Base.fsti"
                                                         (Prims.of_int (406))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (409))
                                                         (Prims.of_int (46)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Steel.ST.GenElim1.Base.fsti"
                                                         (Prims.of_int (404))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (437))
                                                         (Prims.of_int (13)))))
                                                (Obj.magic uu___6)
                                                (fun uu___7 ->
                                                   (fun uu___7 ->
                                                      match uu___7 with
                                                      | (ty, body) ->
                                                          let uu___8 =
                                                            FStarC_Tactics_V1_Builtins.inspect
                                                              body in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (36)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (21)))))
                                                               (Obj.magic
                                                                  uu___8)
                                                               (fun uu___9 ->
                                                                  (fun uu___9
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Abs
                                                                    (b,
                                                                    abody) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    term_has_head
                                                                    abody
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "Util";
                                                                    "exists_"]))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.op_Negation
                                                                    uu___12)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    if
                                                                    uu___11
                                                                    then
                                                                    let uu___12
                                                                    =
                                                                    solve_gen_unit_elim
                                                                    abody in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    body' ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStar_Tactics_V1_Derived.mk_abs
                                                                    [b] body' in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (uu___17,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    [uu___16])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_List_Tot_Base.append
                                                                    ty
                                                                    uu___15)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (match universe
                                                                    with
                                                                    | 
                                                                    uu___16
                                                                    when
                                                                    uu___16 =
                                                                    Prims.int_zero
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExistsUnit0"]))
                                                                    | 
                                                                    uu___16
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExistsUnit1"])))
                                                                    uu___14))))
                                                                    uu___13))
                                                                    else
                                                                    (let uu___13
                                                                    =
                                                                    solve_gen_elim
                                                                    abody in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    body' ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStar_Tactics_V1_Derived.mk_abs
                                                                    [b] body' in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (uu___18,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    [uu___17])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_List_Tot_Base.append
                                                                    ty
                                                                    uu___16)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (match universe
                                                                    with
                                                                    | 
                                                                    uu___17
                                                                    when
                                                                    uu___17 =
                                                                    Prims.int_zero
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExists0"]))
                                                                    | 
                                                                    uu___17
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExists1"])))
                                                                    uu___15))))
                                                                    uu___14))))
                                                                    uu___11)))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (match universe
                                                                    with
                                                                    | 
                                                                    uu___12
                                                                    when
                                                                    uu___12 =
                                                                    Prims.int_zero
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExistsNoAbs0"]))
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExistsNoAbs1"])))
                                                                    lbody))))
                                                                    uu___9)))
                                                     uu___7))) uu___6))
                              else
                                (let uu___6 = is_star_or_vstar hd in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Steel.ST.GenElim1.Base.fsti"
                                               (Prims.of_int (438))
                                               (Prims.of_int (16))
                                               (Prims.of_int (438))
                                               (Prims.of_int (35)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Steel.ST.GenElim1.Base.fsti"
                                               (Prims.of_int (438))
                                               (Prims.of_int (13))
                                               (Prims.of_int (458))
                                               (Prims.of_int (68)))))
                                      (Obj.magic uu___6)
                                      (fun uu___7 ->
                                         (fun uu___7 ->
                                            if uu___7
                                            then
                                              Obj.magic
                                                (Obj.repr
                                                   (match lbody with
                                                    | (tl,
                                                       FStarC_Reflection_V1_Data.Q_Explicit)::
                                                        (tr,
                                                         FStarC_Reflection_V1_Data.Q_Explicit)::[]
                                                        ->
                                                        Obj.repr
                                                          (let uu___8 =
                                                             term_has_head tl
                                                               (FStarC_Reflection_V2_Builtins.pack_ln
                                                                  (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "Util";
                                                                    "exists_"]))) in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (42)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (72)))))
                                                             (Obj.magic
                                                                uu___8)
                                                             (fun uu___9 ->
                                                                (fun uu___9
                                                                   ->
                                                                   if uu___9
                                                                   then
                                                                    let uu___10
                                                                    =
                                                                    solve_gen_elim
                                                                    tl in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun tl'1
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    term_has_head
                                                                    tr
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "Util";
                                                                    "exists_"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    if
                                                                    uu___12
                                                                    then
                                                                    let uu___13
                                                                    =
                                                                    solve_gen_elim
                                                                    tr in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun tr'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEStar"])))
                                                                    [
                                                                    (tl'1,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (tr',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)])))
                                                                    else
                                                                    (let uu___14
                                                                    =
                                                                    solve_gen_unit_elim
                                                                    tr in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun tr'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEStarL"])))
                                                                    [
                                                                    (tl'1,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (tr',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)])))))
                                                                    uu___12)))
                                                                    uu___11))
                                                                   else
                                                                    (let uu___11
                                                                    =
                                                                    solve_gen_unit_elim
                                                                    tl in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (72)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun tl'1
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    solve_gen_elim
                                                                    tr in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (72)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun tr'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEStarR"])))
                                                                    [
                                                                    (tl'1,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (tr',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)]))))
                                                                    uu___12))))
                                                                  uu___9))
                                                    | uu___8 ->
                                                        Obj.repr
                                                          (FStar_Tactics_V1_Derived.fail
                                                             "ill-formed star")))
                                            else
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___9 ->
                                                         FStar_Reflection_V1_Derived.mk_app
                                                           (FStarC_Reflection_V2_Builtins.pack_ln
                                                              (FStarC_Reflection_V2_Data.Tv_FVar
                                                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEUnit"])))
                                                           [((FStar_Reflection_V1_Derived.mk_app
                                                                (FStarC_Reflection_V2_Builtins.pack_ln
                                                                   (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GUEId"])))
                                                                lbody),
                                                              FStarC_Reflection_V1_Data.Q_Explicit)]))))
                                           uu___7)))) uu___4)))) uu___1)
let rec (solve_gen_elim_nondep' :
  Prims.nat ->
    (FStarC_Reflection_Types.term * FStarC_Reflection_Types.binder) Prims.list
      ->
      FStarC_Reflection_Types.term ->
        ((FStarC_Reflection_Types.term * FStarC_Reflection_Types.term *
           FStarC_Reflection_Types.term * FStarC_Reflection_Types.term *
           FStarC_Reflection_Types.term) FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun fuel ->
           fun rev_types_and_binders ->
             fun t ->
               if fuel = Prims.int_zero
               then
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ -> FStar_Pervasives_Native.None)))
               else
                 Obj.magic
                   (Obj.repr
                      (let uu___1 =
                         FStar_Tactics_V1_SyntaxHelpers.collect_app t in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Steel.ST.GenElim1.Base.fsti"
                                  (Prims.of_int (547)) (Prims.of_int (19))
                                  (Prims.of_int (547)) (Prims.of_int (34)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Steel.ST.GenElim1.Base.fsti"
                                  (Prims.of_int (546)) (Prims.of_int (6))
                                  (Prims.of_int (592)) (Prims.of_int (13)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun uu___2 ->
                               match uu___2 with
                               | (hd, tl) ->
                                   if
                                     is_fvar hd "Steel.ST.GenElim1.Base.TRet"
                                   then
                                     (match tl with
                                      | (v,
                                         FStarC_Reflection_V1_Data.Q_Explicit)::
                                          (p,
                                           FStarC_Reflection_V1_Data.Q_Explicit)::[]
                                          ->
                                          Obj.magic
                                            (Obj.repr
                                               (let uu___3 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___4 ->
                                                          fun accu ->
                                                            fun tb ->
                                                              fun uu___5 ->
                                                                let uu___6 =
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    tb)) in
                                                                FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (552))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (552))
                                                                    (Prims.of_int (24)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (88)))))
                                                                  (Obj.magic
                                                                    uu___6)
                                                                  (fun uu___7
                                                                    ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (ty,
                                                                    uu___8)
                                                                    ->
                                                                    let uu___9
                                                                    = accu () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (553))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (553))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun tl1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "Cons"])))
                                                                    [
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Type
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero))))),
                                                                    FStarC_Reflection_V1_Data.Q_Implicit);
                                                                    (ty,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (tl1,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)]))))
                                                                    uu___7))) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Steel.ST.GenElim1.Base.fsti"
                                                           (Prims.of_int (551))
                                                           (Prims.of_int (96))
                                                           (Prims.of_int (554))
                                                           (Prims.of_int (88)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Steel.ST.GenElim1.Base.fsti"
                                                           (Prims.of_int (555))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (582))
                                                           (Prims.of_int (9)))))
                                                  (Obj.magic uu___3)
                                                  (fun uu___4 ->
                                                     (fun cons_type ->
                                                        let uu___4 =
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___6 ->
                                                                  fun uu___5
                                                                    ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "Nil"])))
                                                                    [
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Type
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero))))),
                                                                    FStarC_Reflection_V1_Data.Q_Implicit)])))
                                                                    uu___6
                                                                    uu___5)) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (84)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                             (Obj.magic
                                                                uu___4)
                                                             (fun uu___5 ->
                                                                (fun nil_type
                                                                   ->
                                                                   let uu___5
                                                                    =
                                                                    FStar_List_Tot_Base.fold_left
                                                                    cons_type
                                                                    nil_type
                                                                    rev_types_and_binders
                                                                    () in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    type_list
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    FStar_Tactics_V1_Derived.try_with
                                                                    (fun
                                                                    uu___7 ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_Tactics_V1_Derived.cur_env
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (563))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun env
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.tc
                                                                    env
                                                                    type_list in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (563))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (563))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.term_eq_old
                                                                    ty
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "list"]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Type
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero))))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))))
                                                                    uu___10)))
                                                                    uu___9))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    false)))
                                                                    uu___7) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (564))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (566))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    type_list_typechecks
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    type_list_typechecks
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    FStar_Tactics_V1_Derived.fresh_binder
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_UInst
                                                                    ((FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Universe";
                                                                    "raise_t"]),
                                                                    [
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Unk;
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero))))]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"]))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    dummy_raised_unit_binder
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_List_Tot_Base.append
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.snd
                                                                    (FStar_List_Tot_Base.rev
                                                                    rev_types_and_binders))
                                                                    [dummy_raised_unit_binder])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (120)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    binders
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.norm_term
                                                                    [
                                                                    FStar_Pervasives.delta_attr
                                                                    ["Steel.ST.GenElim1.Base.gen_elim_reduce"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    norm_term
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStar_Tactics_V1_Derived.mk_abs
                                                                    binders v in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun v'
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_UInst
                                                                    ((FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "curried_function_type"]),
                                                                    [
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero));
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero))))])))
                                                                    [
                                                                    (type_list,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Arrow
                                                                    ((FStarC_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStarC_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_UInst
                                                                    ((FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Universe";
                                                                    "raise_t"]),
                                                                    [
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Unk;
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero))))]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"]))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))));
                                                                    FStarC_Reflection_V2_Data.qual
                                                                    =
                                                                    FStarC_Reflection_V2_Data.Q_Explicit;
                                                                    FStarC_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStarC_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "_")
                                                                    }),
                                                                    (FStarC_Reflection_V2_Builtins.pack_comp
                                                                    (FStarC_Reflection_V2_Data.C_Total
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "Effect";
                                                                    "Common";
                                                                    "vprop"])))))))),
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (151)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun tv'
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    FStar_Tactics_V1_Derived.mk_abs
                                                                    binders p in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun p'
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_UInst
                                                                    ((FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "curried_function_type"]),
                                                                    [
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero));
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero))))])))
                                                                    [
                                                                    (type_list,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Arrow
                                                                    ((FStarC_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStarC_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_UInst
                                                                    ((FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Universe";
                                                                    "raise_t"]),
                                                                    [
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Unk;
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    (FStarC_Reflection_V2_Data.Uv_Succ
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero))))]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"]))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))));
                                                                    FStarC_Reflection_V2_Data.qual
                                                                    =
                                                                    FStarC_Reflection_V2_Data.Q_Explicit;
                                                                    FStarC_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStarC_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "_")
                                                                    }),
                                                                    (FStarC_Reflection_V2_Builtins.pack_comp
                                                                    (FStarC_Reflection_V2_Data.C_Total
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "prop"])))))))),
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (150)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun tp'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (type_list,
                                                                    tv', v',
                                                                    tp', p')))))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9))))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                  uu___5)))
                                                       uu___4)))
                                      | uu___3 ->
                                          Obj.magic
                                            (Obj.repr
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___4 ->
                                                     FStar_Pervasives_Native.None))))
                                   else
                                     if
                                       is_fvar hd
                                         "Steel.ST.GenElim1.Base.TExists"
                                     then
                                       Obj.magic
                                         (Obj.repr
                                            (match tl with
                                             | (ty, uu___4)::(f,
                                                              FStarC_Reflection_V1_Data.Q_Explicit)::[]
                                                 ->
                                                 Obj.repr
                                                   (let uu___5 =
                                                      FStarC_Tactics_V1_Builtins.inspect
                                                        f in
                                                    FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (587))
                                                               (Prims.of_int (18))
                                                               (Prims.of_int (587))
                                                               (Prims.of_int (29)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (587))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (589))
                                                               (Prims.of_int (17)))))
                                                      (Obj.magic uu___5)
                                                      (fun uu___6 ->
                                                         (fun uu___6 ->
                                                            match uu___6 with
                                                            | FStarC_Reflection_V1_Data.Tv_Abs
                                                                (bv, body) ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (solve_gen_elim_nondep'
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    ((ty, bv)
                                                                    ::
                                                                    rev_types_and_binders)
                                                                    body))
                                                            | uu___7 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pervasives_Native.None))))
                                                           uu___6))
                                             | uu___4 ->
                                                 Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___5 ->
                                                         FStar_Pervasives_Native.None))))
                                     else
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___5 ->
                                                  FStar_Pervasives_Native.None))))
                              uu___2)))) uu___2 uu___1 uu___
let (solve_gen_elim_nondep0 :
  Prims.bool ->
    FStarC_Reflection_Types.term ->
      ((FStarC_Reflection_Types.term * FStarC_Reflection_Types.term *
         FStarC_Reflection_Types.term * FStarC_Reflection_Types.term *
         FStarC_Reflection_Types.term) FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun enable_nondep_opt ->
         fun t ->
           if enable_nondep_opt
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_V1_Derived.try_with
                     (fun uu___ ->
                        match () with
                        | () ->
                            let uu___1 =
                              Obj.magic
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      FStar_Reflection_V1_Derived.mk_app
                                        (FStarC_Reflection_V2_Builtins.pack_ln
                                           (FStarC_Reflection_V2_Data.Tv_FVar
                                              (FStarC_Reflection_V2_Builtins.pack_fv
                                                 ["Steel";
                                                 "ST";
                                                 "GenElim1";
                                                 "Base";
                                                 "compute_gen_elim_tele"])))
                                        [(t,
                                           FStarC_Reflection_V1_Data.Q_Explicit)])) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Steel.ST.GenElim1.Base.fsti"
                                       (Prims.of_int (599))
                                       (Prims.of_int (17))
                                       (Prims.of_int (599))
                                       (Prims.of_int (64)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Steel.ST.GenElim1.Base.fsti"
                                       (Prims.of_int (599))
                                       (Prims.of_int (67))
                                       (Prims.of_int (601))
                                       (Prims.of_int (37)))))
                              (Obj.magic uu___1)
                              (fun uu___2 ->
                                 (fun tele ->
                                    let uu___2 =
                                      FStar_Tactics_V1_Derived.norm_term
                                        [FStar_Pervasives.delta_attr
                                           ["Steel.ST.GenElim1.Base.gen_elim_reduce"];
                                        FStar_Pervasives.zeta;
                                        FStar_Pervasives.iota] tele in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Steel.ST.GenElim1.Base.fsti"
                                                  (Prims.of_int (600))
                                                  (Prims.of_int (15))
                                                  (Prims.of_int (600))
                                                  (Prims.of_int (76)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Steel.ST.GenElim1.Base.fsti"
                                                  (Prims.of_int (601))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (601))
                                                  (Prims.of_int (37)))))
                                         (Obj.magic uu___2)
                                         (fun uu___3 ->
                                            (fun t' ->
                                               Obj.magic
                                                 (solve_gen_elim_nondep'
                                                    (Prims.of_int (15)) [] t'))
                                              uu___3))) uu___2))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> FStar_Pervasives_Native.None)))
                          uu___)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 -> FStar_Pervasives_Native.None)))) uu___1
        uu___
let (solve_gen_elim_nondep :
  Prims.bool ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun enable_nondep_opt ->
    fun t ->
      let uu___ = solve_gen_elim_nondep0 enable_nondep_opt t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (606)) (Prims.of_int (8)) (Prims.of_int (606))
                 (Prims.of_int (50)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (606)) (Prims.of_int (2)) (Prims.of_int (620))
                 (Prims.of_int (9))))) (Obj.magic uu___)
        (fun uu___1 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 ->
                match uu___1 with
                | FStar_Pervasives_Native.None ->
                    FStarC_Reflection_V2_Builtins.pack_ln
                      (FStarC_Reflection_V2_Data.Tv_FVar
                         (FStarC_Reflection_V2_Builtins.pack_fv
                            ["Steel"; "ST"; "GenElim1"; "Base"; "GEDep"]))
                | FStar_Pervasives_Native.Some (type_list, tv', v', tp', p')
                    ->
                    FStar_Reflection_V1_Derived.mk_app
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_UInst
                            ((FStarC_Reflection_V2_Builtins.pack_fv
                                ["Steel";
                                "ST";
                                "GenElim1";
                                "Base";
                                "mk_gen_elim_nondep_by_tac"]),
                              [FStarC_Reflection_V2_Builtins.pack_universe
                                 (FStarC_Reflection_V2_Data.Uv_Succ
                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                       FStarC_Reflection_V2_Data.Uv_Zero))])))
                      [(type_list, FStarC_Reflection_V1_Data.Q_Explicit);
                      (tv', FStarC_Reflection_V1_Data.Q_Explicit);
                      (v', FStarC_Reflection_V1_Data.Q_Explicit);
                      (tp', FStarC_Reflection_V1_Data.Q_Explicit);
                      (p', FStarC_Reflection_V1_Data.Q_Explicit)]))
let (trefl_or_smt : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStar_Tactics_V1_Derived.cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (623)) (Prims.of_int (11)) (Prims.of_int (623))
               (Prims.of_int (24)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (624)) (Prims.of_int (2)) (Prims.of_int (626))
               (Prims.of_int (27))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun ty ->
            let uu___2 = FStar_Reflection_V1_Formula.term_as_formula ty in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                          (Prims.of_int (624)) (Prims.of_int (8))
                          (Prims.of_int (624)) (Prims.of_int (28)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                          (Prims.of_int (624)) (Prims.of_int (2))
                          (Prims.of_int (626)) (Prims.of_int (27)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       match uu___3 with
                       | FStar_Reflection_V1_Formula.Comp
                           (uu___4, uu___5, uu___6) ->
                           Obj.magic (FStar_Tactics_V1_Derived.trefl ())
                       | uu___4 ->
                           let uu___5 = FStar_Tactics_V1_Derived.smt () in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Steel.ST.GenElim1.Base.fsti"
                                         (Prims.of_int (626))
                                         (Prims.of_int (9))
                                         (Prims.of_int (626))
                                         (Prims.of_int (17)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Steel.ST.GenElim1.Base.fsti"
                                         (Prims.of_int (626))
                                         (Prims.of_int (19))
                                         (Prims.of_int (626))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___5)
                                (fun uu___6 ->
                                   (fun uu___6 ->
                                      Obj.magic
                                        (FStar_Tactics_V1_Derived.qed ()))
                                     uu___6))) uu___3))) uu___2)
let (solve_gen_elim_prop :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStar_Tactics_V1_Derived.cur_goal () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (632)) (Prims.of_int (31))
                 (Prims.of_int (632)) (Prims.of_int (46)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (632)) (Prims.of_int (17))
                 (Prims.of_int (632)) (Prims.of_int (46)))))
        (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 ->
              Obj.magic (FStar_Tactics_V1_SyntaxHelpers.collect_app uu___3))
             uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (632)) (Prims.of_int (17)) (Prims.of_int (632))
               (Prims.of_int (46)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (631)) Prims.int_one (Prims.of_int (670))
               (Prims.of_int (35))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | (hd, tl) ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 = is_squash hd in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim1.Base.fsti"
                               (Prims.of_int (633)) (Prims.of_int (9))
                               (Prims.of_int (633)) (Prims.of_int (23)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim1.Base.fsti"
                               (Prims.of_int (633)) (Prims.of_int (5))
                               (Prims.of_int (633)) (Prims.of_int (23)))))
                      (Obj.magic uu___5)
                      (fun uu___6 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___7 -> Prims.op_Negation uu___6)) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                             (Prims.of_int (633)) (Prims.of_int (5))
                             (Prims.of_int (633)) (Prims.of_int (23)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                             (Prims.of_int (633)) (Prims.of_int (2))
                             (Prims.of_int (634)) (Prims.of_int (33)))))
                    (Obj.magic uu___4)
                    (fun uu___5 ->
                       if uu___5
                       then FStar_Tactics_V1_Derived.fail "not a squash goal"
                       else
                         FStar_Tactics_Effect.lift_div_tac (fun uu___7 -> ())) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Steel.ST.GenElim1.Base.fsti"
                              (Prims.of_int (633)) (Prims.of_int (2))
                              (Prims.of_int (634)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Steel.ST.GenElim1.Base.fsti"
                              (Prims.of_int (635)) (Prims.of_int (2))
                              (Prims.of_int (670)) (Prims.of_int (35)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 ->
                           match tl with
                           | (body1, FStarC_Reflection_V1_Data.Q_Explicit)::[]
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___5 =
                                       FStar_Tactics_V1_SyntaxHelpers.collect_app
                                         body1 in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (637))
                                                (Prims.of_int (21))
                                                (Prims.of_int (637))
                                                (Prims.of_int (40)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (636))
                                                (Prims.of_int (28))
                                                (Prims.of_int (669))
                                                (Prims.of_int (7)))))
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun uu___6 ->
                                             match uu___6 with
                                             | (hd1, tl1) ->
                                                 let uu___7 =
                                                   if
                                                     Prims.op_Negation
                                                       (is_fvar hd1
                                                          "Steel.ST.GenElim1.Base.gen_elim_prop")
                                                   then
                                                     Obj.magic
                                                       (FStar_Tactics_V1_Derived.fail
                                                          "not a gen_elim_prop goal")
                                                   else
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___9 -> ())) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (638))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (639))
                                                               (Prims.of_int (42)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (640))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (668))
                                                               (Prims.of_int (44)))))
                                                      (Obj.magic uu___7)
                                                      (fun uu___8 ->
                                                         (fun uu___8 ->
                                                            match FStar_List_Tot_Base.filter
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (uu___10,
                                                                    x) ->
                                                                    FStarC_Reflection_V1_Data.uu___is_Q_Explicit
                                                                    x) tl1
                                                            with
                                                            | (enable_nondep_opt_tm,
                                                               uu___9)::
                                                                (p, uu___10)::
                                                                (a, uu___11)::
                                                                (q, uu___12)::
                                                                (post,
                                                                 uu___13)::[]
                                                                ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (let uu___14
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_eq_old
                                                                    enable_nondep_opt_tm
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_True)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    enable_nondep_opt
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    solve_gen_elim
                                                                    p in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun i'
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    fun
                                                                    uu___18
                                                                    ->
                                                                    FStarC_Tactics_V1_Builtins.norm
                                                                    [
                                                                    FStar_Pervasives.delta_attr
                                                                    ["Steel.ST.GenElim1.Base.gen_elim_reduce"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun norm
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    solve_gen_elim_nondep0
                                                                    enable_nondep_opt
                                                                    i' in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.apply_lemma
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "gen_elim_prop_intro'"])))
                                                                    [
                                                                    (i',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEDep"]))),
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)]))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (type_list,
                                                                    tvprop,
                                                                    q0,
                                                                    tprop,
                                                                    post0) ->
                                                                    let uu___20
                                                                    =
                                                                    FStar_Tactics_V1_Derived.apply_lemma
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "gen_elim_prop_intro"])))
                                                                    [
                                                                    (i',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (type_list,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (tvprop,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (q0,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (tprop,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (post0,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    let uu___24
                                                                    = norm () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___25)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    let uu___25
                                                                    = norm () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___26))))
                                                                    uu___23)))
                                                                    uu___21)))
                                                                    uu___19) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    = norm () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___22)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    let uu___23
                                                                    = norm () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    Obj.magic
                                                                    (trefl_or_smt
                                                                    ()))
                                                                    uu___24)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    let uu___25
                                                                    = norm () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___26)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    let uu___27
                                                                    = norm () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___28)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    let uu___28
                                                                    = norm () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___29))))
                                                                    uu___26)))
                                                                    uu___24)))
                                                                    uu___22)))
                                                                    uu___20)))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                            | uu___9 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_V1_Derived.fail
                                                                    "ill formed gen_elim_prop")))
                                                           uu___8))) uu___6)))
                           | uu___5 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_V1_Derived.fail
                                       "ill-formed squash"))) uu___4)))
           uu___2)
let (solve_gen_elim_prop_placeholder :
  unit -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStar_Tactics_V1_Derived.cur_goal () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (676)) (Prims.of_int (31))
                 (Prims.of_int (676)) (Prims.of_int (46)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (676)) (Prims.of_int (17))
                 (Prims.of_int (676)) (Prims.of_int (46)))))
        (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 ->
              Obj.magic (FStar_Tactics_V1_SyntaxHelpers.collect_app uu___3))
             uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (676)) (Prims.of_int (17)) (Prims.of_int (676))
               (Prims.of_int (46)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (675)) Prims.int_one (Prims.of_int (712))
               (Prims.of_int (35))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | (hd, tl) ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 = is_squash hd in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim1.Base.fsti"
                               (Prims.of_int (677)) (Prims.of_int (9))
                               (Prims.of_int (677)) (Prims.of_int (23)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim1.Base.fsti"
                               (Prims.of_int (677)) (Prims.of_int (5))
                               (Prims.of_int (677)) (Prims.of_int (23)))))
                      (Obj.magic uu___5)
                      (fun uu___6 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___7 -> Prims.op_Negation uu___6)) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                             (Prims.of_int (677)) (Prims.of_int (5))
                             (Prims.of_int (677)) (Prims.of_int (23)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                             (Prims.of_int (677)) (Prims.of_int (2))
                             (Prims.of_int (678)) (Prims.of_int (33)))))
                    (Obj.magic uu___4)
                    (fun uu___5 ->
                       if uu___5
                       then FStar_Tactics_V1_Derived.fail "not a squash goal"
                       else
                         FStar_Tactics_Effect.lift_div_tac (fun uu___7 -> ())) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Steel.ST.GenElim1.Base.fsti"
                              (Prims.of_int (677)) (Prims.of_int (2))
                              (Prims.of_int (678)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Steel.ST.GenElim1.Base.fsti"
                              (Prims.of_int (679)) (Prims.of_int (2))
                              (Prims.of_int (712)) (Prims.of_int (35)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 ->
                           match tl with
                           | (body1, FStarC_Reflection_V1_Data.Q_Explicit)::[]
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___5 =
                                       FStar_Tactics_V1_SyntaxHelpers.collect_app
                                         body1 in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (681))
                                                (Prims.of_int (21))
                                                (Prims.of_int (681))
                                                (Prims.of_int (40)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (680))
                                                (Prims.of_int (28))
                                                (Prims.of_int (711))
                                                (Prims.of_int (7)))))
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun uu___6 ->
                                             match uu___6 with
                                             | (hd1, tl1) ->
                                                 let uu___7 =
                                                   if
                                                     Prims.op_Negation
                                                       (is_fvar hd1
                                                          "Steel.ST.GenElim1.Base.gen_elim_prop_placeholder")
                                                   then
                                                     Obj.magic
                                                       (FStar_Tactics_V1_Derived.fail
                                                          "not a gen_elim_prop_placeholder goal")
                                                   else
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___9 -> ())) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (682))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (683))
                                                               (Prims.of_int (54)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (684))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (710))
                                                               (Prims.of_int (56)))))
                                                      (Obj.magic uu___7)
                                                      (fun uu___8 ->
                                                         (fun uu___8 ->
                                                            match FStar_List_Tot_Base.filter
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (uu___10,
                                                                    x) ->
                                                                    FStarC_Reflection_V1_Data.uu___is_Q_Explicit
                                                                    x) tl1
                                                            with
                                                            | (enable_nondep_opt_tm,
                                                               uu___9)::
                                                                (p, uu___10)::
                                                                (a, uu___11)::
                                                                (q, uu___12)::
                                                                (post,
                                                                 uu___13)::[]
                                                                ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    Steel_Effect_Common.slterm_nbr_uvars
                                                                    p in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    uu___17
                                                                    <>
                                                                    Prims.int_zero)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    if
                                                                    uu___16
                                                                    then
                                                                    FStar_Tactics_V1_Derived.fail
                                                                    "pre-resource not solved yet"
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    -> ())) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.inspect
                                                                    a in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStarC_Reflection_V1_Data.uu___is_Tv_Uvar
                                                                    uu___18)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    a_is_uvar
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.inspect
                                                                    q in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStarC_Reflection_V1_Data.uu___is_Tv_Uvar
                                                                    uu___19)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    q_is_uvar
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.inspect
                                                                    post in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStarC_Reflection_V1_Data.uu___is_Tv_Uvar
                                                                    uu___20)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    post_is_uvar
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    if
                                                                    Prims.op_Negation
                                                                    ((a_is_uvar
                                                                    &&
                                                                    q_is_uvar)
                                                                    &&
                                                                    post_is_uvar)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.fail
                                                                    "gen_elim_prop_placeholder is already solved")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_eq_old
                                                                    enable_nondep_opt_tm
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_True)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    enable_nondep_opt
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    solve_gen_elim
                                                                    p in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun i'
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    solve_gen_elim_nondep
                                                                    enable_nondep_opt
                                                                    i' in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun j'
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.norm_term
                                                                    [
                                                                    FStar_Pervasives.delta_attr
                                                                    ["Steel.ST.GenElim1.Base.gen_elim_reduce"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    norm_term
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "compute_gen_elim_nondep_a"])))
                                                                    [
                                                                    (i',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (j',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun a'
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    a' in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    a'_ts ->
                                                                    let uu___27
                                                                    =
                                                                    norm_term
                                                                    a' in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun a'1
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "compute_gen_elim_nondep_q"])))
                                                                    [
                                                                    (i',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (j',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun q'
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "compute_gen_elim_nondep_post"])))
                                                                    [
                                                                    (i',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (j',
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (701))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (701))
                                                                    (Prims.of_int (107)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (fun
                                                                    post' ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.unshelve
                                                                    a in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (703))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStar_Tactics_V1_Derived.exact
                                                                    a'1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (703))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (703))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.unshelve
                                                                    q in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (705))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    FStar_Tactics_V1_Derived.exact
                                                                    q' in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (705))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (705))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.unshelve
                                                                    post in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    FStar_Tactics_V1_Derived.exact
                                                                    post' in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___40)
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    let uu___42
                                                                    =
                                                                    FStar_Tactics_V1_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "gen_elim_prop_placeholder_intro"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___42)
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___44
                                                                    -> true))))
                                                                    uu___41)))
                                                                    uu___39)))
                                                                    uu___37)))
                                                                    uu___35)))
                                                                    uu___33)))
                                                                    uu___31)))
                                                                    uu___30)))
                                                                    uu___29)))
                                                                    uu___28)))
                                                                    uu___27)))
                                                                    uu___26)))
                                                                    uu___25)))
                                                                    uu___24)))
                                                                    uu___23)))
                                                                    uu___22)))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___15)))
                                                            | uu___9 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_V1_Derived.fail
                                                                    "ill-formed gen_elim_prop_placeholder")))
                                                           uu___8))) uu___6)))
                           | uu___5 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_V1_Derived.fail
                                       "ill-formed squash"))) uu___4)))
           uu___2)
let (init_resolve_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    Steel_Effect_Common.init_resolve_tac'
      [((FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["Steel";
                 "ST";
                 "GenElim1";
                 "Base";
                 "gen_elim_prop_placeholder"]))),
         solve_gen_elim_prop_placeholder)]
let _ =
  FStarC_Tactics_Native.register_tactic
    "Steel.ST.GenElim1.Base.init_resolve_tac" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
               "Steel.ST.GenElim1.Base.init_resolve_tac (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 init_resolve_tac)
               FStarC_Syntax_Embeddings.e_unit FStarC_Syntax_Embeddings.e_unit
               psc ncb us args)