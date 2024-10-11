open Prims
let (is_fvar : FStar_Reflection_Types.term -> Prims.string -> Prims.bool) =
  FStar_Reflection_V1_Derived.is_fvar
let (is_any_fvar :
  FStar_Reflection_Types.term -> Prims.string Prims.list -> Prims.bool) =
  FStar_Reflection_V1_Derived.is_any_fvar
let (is_squash :
  FStar_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ -> is_any_fvar t ["Prims.squash"; "Prims.auto_squash"])))
      uu___
let (is_star_or_vstar :
  FStar_Reflection_Types.term ->
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
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun head ->
      let uu___ = FStar_Tactics_V1_SyntaxHelpers.collect_app t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (309)) (Prims.of_int (17))
                 (Prims.of_int (309)) (Prims.of_int (32)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (309)) Prims.int_one (Prims.of_int (320))
                 (Prims.of_int (12))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (hd, tl) ->
                  let uu___2 = FStar_Tactics_V1_Builtins.term_eq_old hd head in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Steel.ST.GenElim.Base.fsti"
                                (Prims.of_int (310)) (Prims.of_int (5))
                                (Prims.of_int (310)) (Prims.of_int (28)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Steel.ST.GenElim.Base.fsti"
                                (Prims.of_int (310)) (Prims.of_int (2))
                                (Prims.of_int (320)) (Prims.of_int (12)))))
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
                                                "Steel.ST.GenElim.Base.fsti"
                                                (Prims.of_int (312))
                                                (Prims.of_int (10))
                                                (Prims.of_int (312))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim.Base.fsti"
                                                (Prims.of_int (312))
                                                (Prims.of_int (7))
                                                (Prims.of_int (320))
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
                                                        FStar_Reflection_V1_Data.Q_Explicit)::
                                                         (td,
                                                          FStar_Reflection_V1_Data.Q_Explicit)::[]
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (30)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (318))
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
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tl' ->
    let uu___ =
      let uu___1 =
        term_has_head tl'
          (FStar_Reflection_V2_Builtins.pack_ln
             (FStar_Reflection_V2_Data.Tv_FVar
                (FStar_Reflection_V2_Builtins.pack_fv
                   ["Steel"; "ST"; "Util"; "pure"]))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (326)) (Prims.of_int (13))
                 (Prims.of_int (326)) (Prims.of_int (40)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (326)) (Prims.of_int (9)) (Prims.of_int (326))
                 (Prims.of_int (40))))) (Obj.magic uu___1)
        (fun uu___2 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___3 -> Prims.op_Negation uu___2)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
               (Prims.of_int (326)) (Prims.of_int (9)) (Prims.of_int (326))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
               (Prims.of_int (326)) (Prims.of_int (6)) (Prims.of_int (340))
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
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["Steel";
                                    "ST";
                                    "GenElim";
                                    "Base";
                                    "GUEId"])))
                           [(tl', FStar_Reflection_V1_Data.Q_Explicit)])))
            else
              Obj.magic
                (Obj.repr
                   (let uu___3 =
                      FStar_Tactics_V1_SyntaxHelpers.collect_app tl' in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim.Base.fsti"
                               (Prims.of_int (329)) (Prims.of_int (23))
                               (Prims.of_int (329)) (Prims.of_int (40)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim.Base.fsti"
                               (Prims.of_int (328)) (Prims.of_int (10))
                               (Prims.of_int (340)) (Prims.of_int (47)))))
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
                                               (FStar_Reflection_V2_Builtins.pack_ln
                                                  (FStar_Reflection_V2_Data.Tv_FVar
                                                     (FStar_Reflection_V2_Builtins.pack_fv
                                                        ["Steel";
                                                        "ST";
                                                        "GenElim";
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
                                                   "Steel.ST.GenElim.Base.fsti"
                                                   (Prims.of_int (332))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (332))
                                                   (Prims.of_int (35)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Steel.ST.GenElim.Base.fsti"
                                                   (Prims.of_int (332))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (340))
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
                                                           FStar_Reflection_V1_Data.Q_Explicit)::
                                                            (t2,
                                                             FStar_Reflection_V1_Data.Q_Explicit)::[]
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (42)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (337))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (337))
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
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "GUEStar"])))
                                                                    [
                                                                    (t1',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (t2',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]))))
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
                                                               (FStar_Reflection_V2_Builtins.pack_ln
                                                                  (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "GUEId"])))
                                                               [(tl',
                                                                  FStar_Reflection_V1_Data.Q_Explicit)]))))
                                               uu___7)))) uu___4)))) uu___1)
let (abstr_has_exists :
  FStar_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_V1_Builtins.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
               (Prims.of_int (345)) (Prims.of_int (8)) (Prims.of_int (345))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
               (Prims.of_int (345)) (Prims.of_int (2)) (Prims.of_int (347))
               (Prims.of_int (14))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Reflection_V1_Data.Tv_Abs (uu___2, body) ->
                Obj.magic
                  (Obj.repr
                     (term_has_head body
                        (FStar_Reflection_V2_Builtins.pack_ln
                           (FStar_Reflection_V2_Data.Tv_FVar
                              (FStar_Reflection_V2_Builtins.pack_fv
                                 ["Steel"; "ST"; "Util"; "exists_"])))))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> false))))
           uu___1)
let rec (solve_gen_elim :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tl' ->
    let uu___ =
      let uu___1 =
        term_has_head tl'
          (FStar_Reflection_V2_Builtins.pack_ln
             (FStar_Reflection_V2_Data.Tv_FVar
                (FStar_Reflection_V2_Builtins.pack_fv
                   ["Steel"; "ST"; "Util"; "exists_"]))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (353)) (Prims.of_int (13))
                 (Prims.of_int (353)) (Prims.of_int (43)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (353)) (Prims.of_int (9)) (Prims.of_int (353))
                 (Prims.of_int (43))))) (Obj.magic uu___1)
        (fun uu___2 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___3 -> Prims.op_Negation uu___2)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
               (Prims.of_int (353)) (Prims.of_int (9)) (Prims.of_int (353))
               (Prims.of_int (43)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
               (Prims.of_int (353)) (Prims.of_int (6)) (Prims.of_int (399))
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
                         (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                            (Prims.of_int (355)) (Prims.of_int (17))
                            (Prims.of_int (355)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                            (Prims.of_int (356)) (Prims.of_int (8))
                            (Prims.of_int (356)) (Prims.of_int (45)))))
                   (Obj.magic uu___2)
                   (fun t' ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           FStar_Reflection_V1_Derived.mk_app
                             (FStar_Reflection_V2_Builtins.pack_ln
                                (FStar_Reflection_V2_Data.Tv_FVar
                                   (FStar_Reflection_V2_Builtins.pack_fv
                                      ["Steel";
                                      "ST";
                                      "GenElim";
                                      "Base";
                                      "GEUnit"])))
                             [(t', FStar_Reflection_V1_Data.Q_Explicit)])))
            else
              (let uu___3 = FStar_Tactics_V1_SyntaxHelpers.collect_app tl' in
               Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                             (Prims.of_int (358)) (Prims.of_int (26))
                             (Prims.of_int (358)) (Prims.of_int (43)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                             (Prims.of_int (357)) (Prims.of_int (14))
                             (Prims.of_int (399)) (Prims.of_int (68)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       (fun uu___4 ->
                          match uu___4 with
                          | (hd, lbody) ->
                              if is_fvar hd "Steel.ST.Util.exists_"
                              then
                                let uu___5 =
                                  match lbody with
                                  | (ty, FStar_Reflection_V1_Data.Q_Implicit)::
                                      (body,
                                       FStar_Reflection_V1_Data.Q_Explicit)::[]
                                      ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___6 ->
                                              ([(ty,
                                                  FStar_Reflection_V1_Data.Q_Implicit)],
                                                body)))
                                  | (body,
                                     FStar_Reflection_V1_Data.Q_Explicit)::[]
                                      ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___6 -> ([], body)))
                                  | uu___6 ->
                                      Obj.magic
                                        (FStar_Tactics_V1_Derived.fail
                                           "ill-formed exists_") in
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Steel.ST.GenElim.Base.fsti"
                                              (Prims.of_int (362))
                                              (Prims.of_int (12))
                                              (Prims.of_int (365))
                                              (Prims.of_int (46)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Steel.ST.GenElim.Base.fsti"
                                              (Prims.of_int (360))
                                              (Prims.of_int (12))
                                              (Prims.of_int (378))
                                              (Prims.of_int (13)))))
                                     (Obj.magic uu___5)
                                     (fun uu___6 ->
                                        (fun uu___6 ->
                                           match uu___6 with
                                           | (ty, body) ->
                                               let uu___7 =
                                                 FStar_Tactics_V1_Builtins.inspect
                                                   body in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Steel.ST.GenElim.Base.fsti"
                                                             (Prims.of_int (367))
                                                             (Prims.of_int (22))
                                                             (Prims.of_int (367))
                                                             (Prims.of_int (36)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Steel.ST.GenElim.Base.fsti"
                                                             (Prims.of_int (367))
                                                             (Prims.of_int (16))
                                                             (Prims.of_int (377))
                                                             (Prims.of_int (45)))))
                                                    (Obj.magic uu___7)
                                                    (fun uu___8 ->
                                                       (fun uu___8 ->
                                                          match uu___8 with
                                                          | FStar_Reflection_V1_Data.Tv_Abs
                                                              (b, abody) ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    term_has_head
                                                                    abody
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "Util";
                                                                    "exists_"]))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Prims.op_Negation
                                                                    uu___11)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (94)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    if
                                                                    uu___10
                                                                    then
                                                                    let uu___11
                                                                    =
                                                                    solve_gen_unit_elim
                                                                    abody in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (98)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    body' ->
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_V1_Derived.mk_abs
                                                                    [b] body' in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (96)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (uu___16,
                                                                    FStar_Reflection_V1_Data.Q_Explicit))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    [uu___15])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (98)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_List_Tot_Base.append
                                                                    ty
                                                                    uu___14)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (98)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "GEExistsUnit"])))
                                                                    uu___13))))
                                                                    uu___12))
                                                                    else
                                                                    (let uu___12
                                                                    =
                                                                    solve_gen_elim
                                                                    abody in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (94)))))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (92)))))
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
                                                                    FStar_Reflection_V1_Data.Q_Explicit))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (93)))))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (94)))))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (94)))))
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
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "GEExists"])))
                                                                    uu___14))))
                                                                    uu___13))))
                                                                    uu___10)))
                                                          | uu___9 ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "GEExistsNoAbs"])))
                                                                    lbody))))
                                                         uu___8))) uu___6))
                              else
                                (let uu___6 = is_star_or_vstar hd in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Steel.ST.GenElim.Base.fsti"
                                               (Prims.of_int (379))
                                               (Prims.of_int (16))
                                               (Prims.of_int (379))
                                               (Prims.of_int (35)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Steel.ST.GenElim.Base.fsti"
                                               (Prims.of_int (379))
                                               (Prims.of_int (13))
                                               (Prims.of_int (399))
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
                                                       FStar_Reflection_V1_Data.Q_Explicit)::
                                                        (tr,
                                                         FStar_Reflection_V1_Data.Q_Explicit)::[]
                                                        ->
                                                        Obj.repr
                                                          (let uu___8 =
                                                             term_has_head tl
                                                               (FStar_Reflection_V2_Builtins.pack_ln
                                                                  (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "Util";
                                                                    "exists_"]))) in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (42)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (396))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (392))
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
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "Util";
                                                                    "exists_"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (392))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (389))
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
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "GEStar"])))
                                                                    [
                                                                    (tl'1,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tr',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)])))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (392))
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
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "GEStarL"])))
                                                                    [
                                                                    (tl'1,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tr',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)])))))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (396))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (396))
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
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "GEStarR"])))
                                                                    [
                                                                    (tl'1,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tr',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]))))
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
                                                           (FStar_Reflection_V2_Builtins.pack_ln
                                                              (FStar_Reflection_V2_Data.Tv_FVar
                                                                 (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "GEUnit"])))
                                                           [((FStar_Reflection_V1_Derived.mk_app
                                                                (FStar_Reflection_V2_Builtins.pack_ln
                                                                   (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "GUEId"])))
                                                                lbody),
                                                              FStar_Reflection_V1_Data.Q_Explicit)]))))
                                           uu___7)))) uu___4)))) uu___1)
let rec (solve_gen_elim_nondep' :
  Prims.nat ->
    (FStar_Reflection_Types.term * FStar_Reflection_Types.binder) Prims.list
      ->
      FStar_Reflection_Types.term ->
        ((FStar_Reflection_Types.term * FStar_Reflection_Types.term *
           FStar_Reflection_Types.term * FStar_Reflection_Types.term *
           FStar_Reflection_Types.term) FStar_Pervasives_Native.option,
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
                                  "Steel.ST.GenElim.Base.fsti"
                                  (Prims.of_int (488)) (Prims.of_int (19))
                                  (Prims.of_int (488)) (Prims.of_int (34)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Steel.ST.GenElim.Base.fsti"
                                  (Prims.of_int (487)) (Prims.of_int (6))
                                  (Prims.of_int (532)) (Prims.of_int (13)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun uu___2 ->
                               match uu___2 with
                               | (hd, tl) ->
                                   if is_fvar hd "Steel.ST.GenElim.Base.TRet"
                                   then
                                     (match tl with
                                      | (v,
                                         FStar_Reflection_V1_Data.Q_Explicit)::
                                          (p,
                                           FStar_Reflection_V1_Data.Q_Explicit)::[]
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (24)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (85)))))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun tl1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "Cons"])))
                                                                    [
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Type
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero))),
                                                                    FStar_Reflection_V1_Data.Q_Implicit);
                                                                    (ty,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tl1,
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]))))
                                                                    uu___7))) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Steel.ST.GenElim.Base.fsti"
                                                           (Prims.of_int (492))
                                                           (Prims.of_int (96))
                                                           (Prims.of_int (495))
                                                           (Prims.of_int (85)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Steel.ST.GenElim.Base.fsti"
                                                           (Prims.of_int (496))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (522))
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
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "Nil"])))
                                                                    [
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Type
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero))),
                                                                    FStar_Reflection_V1_Data.Q_Implicit)])))
                                                                    uu___6
                                                                    uu___5)) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (79)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (522))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (522))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun env
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_V1_Builtins.tc
                                                                    env
                                                                    type_list in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.term_eq_old
                                                                    ty
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "list"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Type
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (507))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (522))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.snd
                                                                    (FStar_List_Tot_Base.rev
                                                                    rev_types_and_binders))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    binders
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.norm_term
                                                                    [
                                                                    FStar_Pervasives.delta_attr
                                                                    ["Steel.ST.GenElim.Base.gen_elim_reduce"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    norm_term
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_V1_Derived.mk_abs
                                                                    binders v in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun v'
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "curried_function_type"])))
                                                                    [
                                                                    (type_list,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "Effect";
                                                                    "Common";
                                                                    "vprop"]))),
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (113)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun tv'
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    FStar_Tactics_V1_Derived.mk_abs
                                                                    binders p in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun p'
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "curried_function_type"])))
                                                                    [
                                                                    (type_list,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "prop"]))),
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (112)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun tp'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (type_list,
                                                                    tv', v',
                                                                    tp', p')))))
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
                                         "Steel.ST.GenElim.Base.TExists"
                                     then
                                       Obj.magic
                                         (Obj.repr
                                            (match tl with
                                             | (ty, uu___4)::(f,
                                                              FStar_Reflection_V1_Data.Q_Explicit)::[]
                                                 ->
                                                 Obj.repr
                                                   (let uu___5 =
                                                      FStar_Tactics_V1_Builtins.inspect
                                                        f in
                                                    FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim.Base.fsti"
                                                               (Prims.of_int (527))
                                                               (Prims.of_int (18))
                                                               (Prims.of_int (527))
                                                               (Prims.of_int (29)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim.Base.fsti"
                                                               (Prims.of_int (527))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (529))
                                                               (Prims.of_int (17)))))
                                                      (Obj.magic uu___5)
                                                      (fun uu___6 ->
                                                         (fun uu___6 ->
                                                            match uu___6 with
                                                            | FStar_Reflection_V1_Data.Tv_Abs
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
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.term * FStar_Reflection_Types.term *
         FStar_Reflection_Types.term * FStar_Reflection_Types.term *
         FStar_Reflection_Types.term) FStar_Pervasives_Native.option,
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
                                        (FStar_Reflection_V2_Builtins.pack_ln
                                           (FStar_Reflection_V2_Data.Tv_FVar
                                              (FStar_Reflection_V2_Builtins.pack_fv
                                                 ["Steel";
                                                 "ST";
                                                 "GenElim";
                                                 "Base";
                                                 "compute_gen_elim_tele"])))
                                        [(t,
                                           FStar_Reflection_V1_Data.Q_Explicit)])) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Steel.ST.GenElim.Base.fsti"
                                       (Prims.of_int (539))
                                       (Prims.of_int (17))
                                       (Prims.of_int (539))
                                       (Prims.of_int (64)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Steel.ST.GenElim.Base.fsti"
                                       (Prims.of_int (539))
                                       (Prims.of_int (67))
                                       (Prims.of_int (541))
                                       (Prims.of_int (37)))))
                              (Obj.magic uu___1)
                              (fun uu___2 ->
                                 (fun tele ->
                                    let uu___2 =
                                      FStar_Tactics_V1_Derived.norm_term
                                        [FStar_Pervasives.delta_attr
                                           ["Steel.ST.GenElim.Base.gen_elim_reduce"];
                                        FStar_Pervasives.zeta;
                                        FStar_Pervasives.iota] tele in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Steel.ST.GenElim.Base.fsti"
                                                  (Prims.of_int (540))
                                                  (Prims.of_int (15))
                                                  (Prims.of_int (540))
                                                  (Prims.of_int (76)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Steel.ST.GenElim.Base.fsti"
                                                  (Prims.of_int (541))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (541))
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
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun enable_nondep_opt ->
    fun t ->
      let uu___ = solve_gen_elim_nondep0 enable_nondep_opt t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (546)) (Prims.of_int (8)) (Prims.of_int (546))
                 (Prims.of_int (50)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (546)) (Prims.of_int (2)) (Prims.of_int (560))
                 (Prims.of_int (9))))) (Obj.magic uu___)
        (fun uu___1 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 ->
                match uu___1 with
                | FStar_Pervasives_Native.None ->
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_FVar
                         (FStar_Reflection_V2_Builtins.pack_fv
                            ["Steel"; "ST"; "GenElim"; "Base"; "GEDep"]))
                | FStar_Pervasives_Native.Some (type_list, tv', v', tp', p')
                    ->
                    FStar_Reflection_V1_Derived.mk_app
                      (FStar_Reflection_V2_Builtins.pack_ln
                         (FStar_Reflection_V2_Data.Tv_FVar
                            (FStar_Reflection_V2_Builtins.pack_fv
                               ["Steel";
                               "ST";
                               "GenElim";
                               "Base";
                               "mk_gen_elim_nondep_by_tac"])))
                      [(type_list, FStar_Reflection_V1_Data.Q_Explicit);
                      (tv', FStar_Reflection_V1_Data.Q_Explicit);
                      (v', FStar_Reflection_V1_Data.Q_Explicit);
                      (tp', FStar_Reflection_V1_Data.Q_Explicit);
                      (p', FStar_Reflection_V1_Data.Q_Explicit)]))
let (solve_gen_elim_prop :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStar_Tactics_V1_Derived.cur_goal () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (566)) (Prims.of_int (31))
                 (Prims.of_int (566)) (Prims.of_int (46)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (566)) (Prims.of_int (17))
                 (Prims.of_int (566)) (Prims.of_int (46)))))
        (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 ->
              Obj.magic (FStar_Tactics_V1_SyntaxHelpers.collect_app uu___3))
             uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
               (Prims.of_int (566)) (Prims.of_int (17)) (Prims.of_int (566))
               (Prims.of_int (46)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
               (Prims.of_int (565)) Prims.int_one (Prims.of_int (604))
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
                               "Steel.ST.GenElim.Base.fsti"
                               (Prims.of_int (567)) (Prims.of_int (9))
                               (Prims.of_int (567)) (Prims.of_int (23)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim.Base.fsti"
                               (Prims.of_int (567)) (Prims.of_int (5))
                               (Prims.of_int (567)) (Prims.of_int (23)))))
                      (Obj.magic uu___5)
                      (fun uu___6 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___7 -> Prims.op_Negation uu___6)) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                             (Prims.of_int (567)) (Prims.of_int (5))
                             (Prims.of_int (567)) (Prims.of_int (23)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                             (Prims.of_int (567)) (Prims.of_int (2))
                             (Prims.of_int (568)) (Prims.of_int (33)))))
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
                           (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                              (Prims.of_int (567)) (Prims.of_int (2))
                              (Prims.of_int (568)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                              (Prims.of_int (569)) (Prims.of_int (2))
                              (Prims.of_int (604)) (Prims.of_int (35)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 ->
                           match tl with
                           | (body1, FStar_Reflection_V1_Data.Q_Explicit)::[]
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
                                                "Steel.ST.GenElim.Base.fsti"
                                                (Prims.of_int (571))
                                                (Prims.of_int (21))
                                                (Prims.of_int (571))
                                                (Prims.of_int (40)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim.Base.fsti"
                                                (Prims.of_int (570))
                                                (Prims.of_int (28))
                                                (Prims.of_int (603))
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
                                                          "Steel.ST.GenElim.Base.gen_elim_prop")
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
                                                               "Steel.ST.GenElim.Base.fsti"
                                                               (Prims.of_int (572))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (573))
                                                               (Prims.of_int (42)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim.Base.fsti"
                                                               (Prims.of_int (574))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (602))
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
                                                                    FStar_Reflection_V1_Data.uu___is_Q_Explicit
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
                                                                    FStar_Tactics_V1_Builtins.term_eq_old
                                                                    enable_nondep_opt_tm
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    FStar_Reflection_V2_Data.C_True)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (601))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (577))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (577))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (577))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (601))
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
                                                                    FStar_Tactics_V1_Builtins.norm
                                                                    [
                                                                    FStar_Pervasives.delta_attr
                                                                    ["Steel.ST.GenElim.Base.gen_elim_reduce"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (601))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (595))
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
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "gen_elim_prop_intro'"])))
                                                                    [
                                                                    (i',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "GEDep"]))),
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]))
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
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "gen_elim_prop_intro"])))
                                                                    [
                                                                    (i',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (type_list,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tvprop,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (q0,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tprop,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (post0,
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (586))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (595))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (594))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (595))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (595))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (601))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (597))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (601))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (55)))))
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
                                                                    FStar_Tactics_V1_Derived.trivial
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.qed
                                                                    ()))
                                                                    uu___26)))
                                                                    uu___24)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (601))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (599))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (601))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (600))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (601))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (601))
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
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (610)) (Prims.of_int (31))
                 (Prims.of_int (610)) (Prims.of_int (46)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                 (Prims.of_int (610)) (Prims.of_int (17))
                 (Prims.of_int (610)) (Prims.of_int (46)))))
        (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 ->
              Obj.magic (FStar_Tactics_V1_SyntaxHelpers.collect_app uu___3))
             uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
               (Prims.of_int (610)) (Prims.of_int (17)) (Prims.of_int (610))
               (Prims.of_int (46)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
               (Prims.of_int (609)) Prims.int_one (Prims.of_int (644))
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
                               "Steel.ST.GenElim.Base.fsti"
                               (Prims.of_int (611)) (Prims.of_int (9))
                               (Prims.of_int (611)) (Prims.of_int (23)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim.Base.fsti"
                               (Prims.of_int (611)) (Prims.of_int (5))
                               (Prims.of_int (611)) (Prims.of_int (23)))))
                      (Obj.magic uu___5)
                      (fun uu___6 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___7 -> Prims.op_Negation uu___6)) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                             (Prims.of_int (611)) (Prims.of_int (5))
                             (Prims.of_int (611)) (Prims.of_int (23)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                             (Prims.of_int (611)) (Prims.of_int (2))
                             (Prims.of_int (612)) (Prims.of_int (33)))))
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
                           (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                              (Prims.of_int (611)) (Prims.of_int (2))
                              (Prims.of_int (612)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Steel.ST.GenElim.Base.fsti"
                              (Prims.of_int (613)) (Prims.of_int (2))
                              (Prims.of_int (644)) (Prims.of_int (35)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 ->
                           match tl with
                           | (body1, FStar_Reflection_V1_Data.Q_Explicit)::[]
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
                                                "Steel.ST.GenElim.Base.fsti"
                                                (Prims.of_int (615))
                                                (Prims.of_int (21))
                                                (Prims.of_int (615))
                                                (Prims.of_int (40)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim.Base.fsti"
                                                (Prims.of_int (614))
                                                (Prims.of_int (28))
                                                (Prims.of_int (643))
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
                                                          "Steel.ST.GenElim.Base.gen_elim_prop_placeholder")
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
                                                               "Steel.ST.GenElim.Base.fsti"
                                                               (Prims.of_int (616))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (617))
                                                               (Prims.of_int (54)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim.Base.fsti"
                                                               (Prims.of_int (618))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (642))
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
                                                                    FStar_Reflection_V1_Data.uu___is_Q_Explicit
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (620))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (621))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (641))
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
                                                                    FStar_Tactics_V1_Builtins.inspect
                                                                    a in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (622))
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
                                                                    FStar_Reflection_V1_Data.uu___is_Tv_Uvar
                                                                    uu___18)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (641))
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
                                                                    FStar_Tactics_V1_Builtins.inspect
                                                                    q in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (623))
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
                                                                    FStar_Reflection_V1_Data.uu___is_Tv_Uvar
                                                                    uu___19)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (641))
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
                                                                    FStar_Tactics_V1_Builtins.inspect
                                                                    post in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (624))
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
                                                                    FStar_Reflection_V1_Data.uu___is_Tv_Uvar
                                                                    uu___20)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (641))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (641))
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
                                                                    FStar_Tactics_V1_Builtins.term_eq_old
                                                                    enable_nondep_opt_tm
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    FStar_Reflection_V2_Data.C_True)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (641))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (641))
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
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (641))
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
                                                                    ["Steel.ST.GenElim.Base.gen_elim_reduce"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (641))
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
                                                                    norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "compute_gen_elim_nondep_a"])))
                                                                    [
                                                                    (i',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (j',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (641))
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
                                                                    norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "compute_gen_elim_nondep_q"])))
                                                                    [
                                                                    (i',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (j',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (632))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (632))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (632))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (641))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun q'
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "compute_gen_elim_nondep_post"])))
                                                                    [
                                                                    (i',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (j',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (107)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (641))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    post' ->
                                                                    let uu___28
                                                                    =
                                                                    FStar_Tactics_V1_Builtins.unshelve
                                                                    a in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (641))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStar_Tactics_V1_Derived.exact
                                                                    a' in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (641))
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
                                                                    FStar_Tactics_V1_Builtins.unshelve
                                                                    q in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (641))
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
                                                                    FStar_Tactics_V1_Derived.exact
                                                                    q' in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (638))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (641))
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
                                                                    FStar_Tactics_V1_Builtins.unshelve
                                                                    post in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (638))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (638))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (641))
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
                                                                    FStar_Tactics_V1_Derived.exact
                                                                    post' in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (641))
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
                                                                    FStar_Tactics_V1_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim";
                                                                    "Base";
                                                                    "gen_elim_prop_placeholder_intro"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim.Base.fsti"
                                                                    (Prims.of_int (641))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (641))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___40)
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___42
                                                                    -> true))))
                                                                    uu___39)))
                                                                    uu___37)))
                                                                    uu___35)))
                                                                    uu___33)))
                                                                    uu___31)))
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
      [((FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_FVar
              (FStar_Reflection_V2_Builtins.pack_fv
                 ["Steel";
                 "ST";
                 "GenElim";
                 "Base";
                 "gen_elim_prop_placeholder"]))),
         solve_gen_elim_prop_placeholder)]
let _ =
  FStar_Tactics_Native.register_tactic
    "Steel.ST.GenElim.Base.init_resolve_tac" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
               "Steel.ST.GenElim.Base.init_resolve_tac (plugin)"
               (FStar_Tactics_Native.from_tactic_1 init_resolve_tac)
               FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
               psc ncb us args)