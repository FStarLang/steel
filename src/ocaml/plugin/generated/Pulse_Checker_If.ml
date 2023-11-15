open Prims
let (compute_iname_join :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  = fun is1 -> fun is2 -> Pulse_Typing.tm_join_inames is1 is2
let (tm_sub_inv_ghost :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.st_comp ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              ((unit, unit, unit) Pulse_Typing.st_typing, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun e ->
                   fun c ->
                     fun is1 ->
                       fun is2 ->
                         fun d ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   Pulse_Typing.T_SubInvsGhost
                                     (g, e, is1, is2, c, (), d)))) uu___5
                uu___4 uu___3 uu___2 uu___1 uu___
let (tm_sub_inv_atomic :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.st_comp ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              ((unit, unit, unit) Pulse_Typing.st_typing, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun e ->
                   fun c ->
                     fun is1 ->
                       fun is2 ->
                         fun d ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   Pulse_Typing.T_SubInvsAtomic
                                     (g, e, is1, is2, c, (), d)))) uu___5
                uu___4 uu___3 uu___2 uu___1 uu___
let (lift_atomic_to_st :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (Pulse_Syntax_Base.comp_st,
            (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2)
  =
  fun g ->
    fun e ->
      fun c ->
        fun d ->
          let uu___ = c in
          match uu___ with
          | Pulse_Syntax_Base.C_STAtomic (uu___1, c_st) ->
              let c' = Pulse_Syntax_Base.C_ST c_st in
              let d' =
                Pulse_Typing.T_Lift
                  (g, e, c, c', d, (Pulse_Typing.Lift_STAtomic_ST (g, c))) in
              Prims.Mkdtuple2 (c', d')
let (lift_ghost_to_atomic :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          ((Pulse_Syntax_Base.comp_st,
             (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun c ->
        fun d ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.If.fst"
                     (Prims.of_int (73)) (Prims.of_int (30))
                     (Prims.of_int (73)) (Prims.of_int (31)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.If.fst"
                     (Prims.of_int (73)) Prims.int_one (Prims.of_int (79))
                     (Prims.of_int (14)))))
            (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> c))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | Pulse_Syntax_Base.C_STGhost (inames, c_st) ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Checker.If.fst"
                                    (Prims.of_int (74)) (Prims.of_int (10))
                                    (Prims.of_int (74)) (Prims.of_int (63)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Checker.If.fst"
                                    (Prims.of_int (79)) (Prims.of_int (2))
                                    (Prims.of_int (79)) (Prims.of_int (14)))))
                           (Obj.magic
                              (Pulse_Checker_Pure.get_non_informative_witness
                                 g (Pulse_Syntax_Base.comp_u c)
                                 (Pulse_Syntax_Base.comp_res c)))
                           (fun w ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   Prims.Mkdtuple2
                                     ((Pulse_Syntax_Base.C_STAtomic
                                         (inames, c_st)),
                                       (Pulse_Typing.T_Lift
                                          (g, e, c,
                                            (Pulse_Syntax_Base.C_STAtomic
                                               (inames, c_st)), d,
                                            (Pulse_Typing.Lift_STGhost_STAtomic
                                               (g, c, w))))))))) uu___)
let (lift_if_branches :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Typing_Env.env ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Syntax_Base.comp_st ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  ((Pulse_Syntax_Base.comp_st, Pulse_Syntax_Base.comp_st,
                     (unit, unit, unit) Pulse_Typing.st_typing,
                     (unit, unit, unit) Pulse_Typing.st_typing)
                     FStar_Pervasives.dtuple4,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g_then ->
    fun e_then ->
      fun c_then ->
        fun e_then_typing ->
          fun g_else ->
            fun e_else ->
              fun c_else ->
                fun e_else_typing ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.If.fst"
                             (Prims.of_int (101)) (Prims.of_int (10))
                             (Prims.of_int (101)) (Prims.of_int (16)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.If.fst"
                             (Prims.of_int (102)) (Prims.of_int (2))
                             (Prims.of_int (133)) (Prims.of_int (56)))))
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> g_then))
                    (fun uu___ ->
                       (fun g ->
                          match (c_then, c_else) with
                          | (Pulse_Syntax_Base.C_STGhost (uu___, uu___1),
                             Pulse_Syntax_Base.C_STGhost (uu___2, uu___3)) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 ->
                                         FStar_Pervasives.Mkdtuple4
                                           (c_then, c_else, e_then_typing,
                                             e_else_typing))))
                          | (Pulse_Syntax_Base.C_STAtomic (uu___, uu___1),
                             Pulse_Syntax_Base.C_STAtomic (uu___2, uu___3))
                              ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 ->
                                         FStar_Pervasives.Mkdtuple4
                                           (c_then, c_else, e_then_typing,
                                             e_else_typing))))
                          | (Pulse_Syntax_Base.C_ST uu___,
                             Pulse_Syntax_Base.C_ST uu___1) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         FStar_Pervasives.Mkdtuple4
                                           (c_then, c_else, e_then_typing,
                                             e_else_typing))))
                          | (Pulse_Syntax_Base.C_STAtomic (uu___, uu___1),
                             Pulse_Syntax_Base.C_ST uu___2) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 ->
                                         match lift_atomic_to_st g_then
                                                 e_then c_then e_then_typing
                                         with
                                         | Prims.Mkdtuple2
                                             (c_then', e_then_typing') ->
                                             FStar_Pervasives.Mkdtuple4
                                               (c_then', c_else,
                                                 e_then_typing',
                                                 e_else_typing))))
                          | (Pulse_Syntax_Base.C_ST uu___,
                             Pulse_Syntax_Base.C_STAtomic (uu___1, uu___2))
                              ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 ->
                                         match lift_atomic_to_st g_else
                                                 e_else c_else e_else_typing
                                         with
                                         | Prims.Mkdtuple2
                                             (c_else', e_else_typing') ->
                                             FStar_Pervasives.Mkdtuple4
                                               (c_then, c_else',
                                                 e_then_typing,
                                                 e_else_typing'))))
                          | (Pulse_Syntax_Base.C_STGhost (uu___, uu___1),
                             Pulse_Syntax_Base.C_STAtomic (uu___2, uu___3))
                              ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.If.fst"
                                               (Prims.of_int (118))
                                               (Prims.of_int (40))
                                               (Prims.of_int (118))
                                               (Prims.of_int (95)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.If.fst"
                                               (Prims.of_int (117))
                                               (Prims.of_int (36))
                                               (Prims.of_int (119))
                                               (Prims.of_int (56)))))
                                      (Obj.magic
                                         (lift_ghost_to_atomic g_then e_then
                                            c_then e_then_typing))
                                      (fun uu___4 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___5 ->
                                              match uu___4 with
                                              | Prims.Mkdtuple2
                                                  (c_then', e_then_typing')
                                                  ->
                                                  FStar_Pervasives.Mkdtuple4
                                                    (c_then', c_else,
                                                      e_then_typing',
                                                      e_else_typing)))))
                          | (Pulse_Syntax_Base.C_STAtomic (uu___, uu___1),
                             Pulse_Syntax_Base.C_STGhost (uu___2, uu___3)) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.If.fst"
                                               (Prims.of_int (122))
                                               (Prims.of_int (40))
                                               (Prims.of_int (122))
                                               (Prims.of_int (95)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.If.fst"
                                               (Prims.of_int (121))
                                               (Prims.of_int (36))
                                               (Prims.of_int (123))
                                               (Prims.of_int (56)))))
                                      (Obj.magic
                                         (lift_ghost_to_atomic g_else e_else
                                            c_else e_else_typing))
                                      (fun uu___4 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___5 ->
                                              match uu___4 with
                                              | Prims.Mkdtuple2
                                                  (c_else', e_else_typing')
                                                  ->
                                                  FStar_Pervasives.Mkdtuple4
                                                    (c_then, c_else',
                                                      e_then_typing,
                                                      e_else_typing')))))
                          | (Pulse_Syntax_Base.C_STGhost (uu___, uu___1),
                             Pulse_Syntax_Base.C_ST uu___2) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.If.fst"
                                               (Prims.of_int (126))
                                               (Prims.of_int (40))
                                               (Prims.of_int (126))
                                               (Prims.of_int (96)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.If.fst"
                                               (Prims.of_int (125))
                                               (Prims.of_int (28))
                                               (Prims.of_int (128))
                                               (Prims.of_int (56)))))
                                      (Obj.magic
                                         (lift_ghost_to_atomic g_then e_then
                                            c_then e_then_typing))
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              match uu___3 with
                                              | Prims.Mkdtuple2
                                                  (c_then', e_then_typing')
                                                  ->
                                                  (match lift_atomic_to_st
                                                           g_then e_then
                                                           c_then'
                                                           e_then_typing'
                                                   with
                                                   | Prims.Mkdtuple2
                                                       (c_then'1,
                                                        e_then_typing'1)
                                                       ->
                                                       FStar_Pervasives.Mkdtuple4
                                                         (c_then'1, c_else,
                                                           e_then_typing'1,
                                                           e_else_typing))))))
                          | (Pulse_Syntax_Base.C_ST uu___,
                             Pulse_Syntax_Base.C_STGhost (uu___1, uu___2)) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.If.fst"
                                               (Prims.of_int (131))
                                               (Prims.of_int (40))
                                               (Prims.of_int (131))
                                               (Prims.of_int (96)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.If.fst"
                                               (Prims.of_int (130))
                                               (Prims.of_int (28))
                                               (Prims.of_int (133))
                                               (Prims.of_int (56)))))
                                      (Obj.magic
                                         (lift_ghost_to_atomic g_else e_else
                                            c_else e_else_typing))
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              match uu___3 with
                                              | Prims.Mkdtuple2
                                                  (c_else', e_else_typing')
                                                  ->
                                                  (match lift_atomic_to_st
                                                           g_else e_else
                                                           c_else'
                                                           e_else_typing'
                                                   with
                                                   | Prims.Mkdtuple2
                                                       (c_else'1,
                                                        e_else_typing'1)
                                                       ->
                                                       FStar_Pervasives.Mkdtuple4
                                                         (c_then, c_else'1,
                                                           e_then_typing,
                                                           e_else_typing'1)))))))
                         uu___)
let (inames_of_comp : Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.term) =
  fun c ->
    match c with
    | Pulse_Syntax_Base.C_ST uu___ -> Pulse_Syntax_Base.tm_emp_inames
    | Pulse_Syntax_Base.C_STAtomic (inames, uu___) -> inames
    | Pulse_Syntax_Base.C_STGhost (inames, uu___) -> inames
let (match_inames :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Typing_Env.env ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Syntax_Base.comp_st ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  ((Pulse_Syntax_Base.comp_st, Pulse_Syntax_Base.comp_st,
                     (unit, unit, unit) Pulse_Typing.st_typing,
                     (unit, unit, unit) Pulse_Typing.st_typing)
                     FStar_Pervasives.dtuple4,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun g_then ->
                     fun e_then ->
                       fun c_then ->
                         fun e_then_typing ->
                           fun g_else ->
                             fun e_else ->
                               fun c_else ->
                                 fun e_else_typing ->
                                   match (c_then, c_else) with
                                   | (Pulse_Syntax_Base.C_ST uu___,
                                      Pulse_Syntax_Base.C_ST uu___1) ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  FStar_Pervasives.Mkdtuple4
                                                    (c_then, c_else,
                                                      e_then_typing,
                                                      e_else_typing))))
                                   | (Pulse_Syntax_Base.C_STAtomic
                                      (inames1, stc_then),
                                      Pulse_Syntax_Base.C_STAtomic
                                      (inames2, stc_else)) ->
                                       Obj.magic
                                         (Obj.repr
                                            (if
                                               Pulse_Syntax_Base.eq_tm
                                                 inames1 inames2
                                             then
                                               Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___ ->
                                                       FStar_Pervasives.Mkdtuple4
                                                         (c_then, c_else,
                                                           e_then_typing,
                                                           e_else_typing)))
                                             else
                                               Obj.repr
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.If.fst"
                                                             (Prims.of_int (173))
                                                             (Prims.of_int (15))
                                                             (Prims.of_int (173))
                                                             (Prims.of_int (49)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.If.fst"
                                                             (Prims.of_int (173))
                                                             (Prims.of_int (52))
                                                             (Prims.of_int (176))
                                                             (Prims.of_int (88)))))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          compute_iname_join
                                                            inames1 inames2))
                                                    (fun uu___1 ->
                                                       (fun is ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (91)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (88)))))
                                                               (Obj.magic
                                                                  (tm_sub_inv_atomic
                                                                    g_then
                                                                    e_then
                                                                    stc_then
                                                                    inames1
                                                                    is
                                                                    e_then_typing))
                                                               (fun uu___1 ->
                                                                  (fun
                                                                    e_then_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (tm_sub_inv_atomic
                                                                    g_else
                                                                    e_else
                                                                    stc_else
                                                                    inames2
                                                                    is
                                                                    e_else_typing))
                                                                    (fun
                                                                    e_else_typing1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    ((Pulse_Syntax_Base.C_STAtomic
                                                                    (is,
                                                                    stc_then)),
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (is,
                                                                    stc_else)),
                                                                    e_then_typing1,
                                                                    e_else_typing1)))))
                                                                    uu___1)))
                                                         uu___1))))
                                   | (Pulse_Syntax_Base.C_STGhost
                                      (inames1, stc_then),
                                      Pulse_Syntax_Base.C_STGhost
                                      (inames2, stc_else)) ->
                                       Obj.magic
                                         (Obj.repr
                                            (if
                                               Pulse_Syntax_Base.eq_tm
                                                 inames1 inames2
                                             then
                                               Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___ ->
                                                       FStar_Pervasives.Mkdtuple4
                                                         (c_then, c_else,
                                                           e_then_typing,
                                                           e_else_typing)))
                                             else
                                               Obj.repr
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.If.fst"
                                                             (Prims.of_int (184))
                                                             (Prims.of_int (15))
                                                             (Prims.of_int (184))
                                                             (Prims.of_int (49)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.If.fst"
                                                             (Prims.of_int (184))
                                                             (Prims.of_int (52))
                                                             (Prims.of_int (187))
                                                             (Prims.of_int (86)))))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          compute_iname_join
                                                            inames1 inames2))
                                                    (fun uu___1 ->
                                                       (fun is ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (90)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (86)))))
                                                               (Obj.magic
                                                                  (tm_sub_inv_ghost
                                                                    g_then
                                                                    e_then
                                                                    stc_then
                                                                    inames1
                                                                    is
                                                                    e_then_typing))
                                                               (fun uu___1 ->
                                                                  (fun
                                                                    e_then_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (90)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (tm_sub_inv_ghost
                                                                    g_else
                                                                    e_else
                                                                    stc_else
                                                                    inames2
                                                                    is
                                                                    e_else_typing))
                                                                    (fun
                                                                    e_else_typing1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    ((Pulse_Syntax_Base.C_STGhost
                                                                    (is,
                                                                    stc_then)),
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (is,
                                                                    stc_else)),
                                                                    e_then_typing1,
                                                                    e_else_typing1)))))
                                                                    uu___1)))
                                                         uu___1))))) uu___7
                    uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (combine_if_branches :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Typing_Env.env ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Syntax_Base.comp_st ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  ((Pulse_Syntax_Base.comp_st,
                     (unit, unit, unit) Pulse_Typing.st_typing,
                     (unit, unit, unit) Pulse_Typing.st_typing)
                     FStar_Pervasives.dtuple3,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g_then ->
    fun e_then ->
      fun c_then ->
        fun e_then_typing ->
          fun g_else ->
            fun e_else ->
              fun c_else ->
                fun e_else_typing ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.If.fst"
                             (Prims.of_int (205)) (Prims.of_int (10))
                             (Prims.of_int (205)) (Prims.of_int (16)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.If.fst"
                             (Prims.of_int (206)) (Prims.of_int (2))
                             (Prims.of_int (214)) (Prims.of_int (50)))))
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> g_then))
                    (fun uu___ ->
                       (fun g ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.If.fst"
                                        (Prims.of_int (206))
                                        (Prims.of_int (2))
                                        (Prims.of_int (207))
                                        (Prims.of_int (75)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.If.fst"
                                        (Prims.of_int (207))
                                        (Prims.of_int (76))
                                        (Prims.of_int (214))
                                        (Prims.of_int (50)))))
                               (if
                                  Prims.op_Negation
                                    (Pulse_Syntax_Base.eq_st_comp
                                       (Pulse_Syntax_Base.st_comp_of_comp
                                          c_then)
                                       (Pulse_Syntax_Base.st_comp_of_comp
                                          c_else))
                                then
                                  Obj.magic
                                    (Obj.repr
                                       (Pulse_Typing_Env.fail g
                                          FStar_Pervasives_Native.None
                                          "Cannot combine then and else branches (different st_comp)"))
                                else
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ()))))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.If.fst"
                                                   (Prims.of_int (209))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (209))
                                                   (Prims.of_int (90)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.If.fst"
                                                   (Prims.of_int (207))
                                                   (Prims.of_int (76))
                                                   (Prims.of_int (214))
                                                   (Prims.of_int (50)))))
                                          (Obj.magic
                                             (lift_if_branches g_then e_then
                                                c_then e_then_typing g_else
                                                e_else c_else e_else_typing))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple4
                                                    (c_then', c_else',
                                                     e_then_typing',
                                                     e_else_typing')
                                                    ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.If.fst"
                                                                  (Prims.of_int (212))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (212))
                                                                  (Prims.of_int (90)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.If.fst"
                                                                  (Prims.of_int (210))
                                                                  (Prims.of_int (62))
                                                                  (Prims.of_int (214))
                                                                  (Prims.of_int (50)))))
                                                         (Obj.magic
                                                            (match_inames
                                                               g_then e_then
                                                               c_then'
                                                               e_then_typing'
                                                               g_else e_else
                                                               c_else'
                                                               e_else_typing'))
                                                         (fun uu___2 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___3 ->
                                                                 match uu___2
                                                                 with
                                                                 | FStar_Pervasives.Mkdtuple4
                                                                    (c_then'',
                                                                    c_else'',
                                                                    e_then_typing'',
                                                                    e_else_typing'')
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c_then'',
                                                                    e_then_typing'',
                                                                    e_else_typing'')))))
                                               uu___1))) uu___))) uu___)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.st_term ->
                Pulse_Syntax_Base.st_term ->
                  Pulse_Checker_Base.check_t ->
                    ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun b ->
              fun e1 ->
                fun e2 ->
                  fun check1 ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.If.fst"
                               (Prims.of_int (228)) (Prims.of_int (10))
                               (Prims.of_int (228)) (Prims.of_int (61)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.If.fst"
                               (Prims.of_int (228)) (Prims.of_int (64))
                               (Prims.of_int (290)) (Prims.of_int (43)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            Pulse_Typing_Env.push_context g "check_if"
                              e1.Pulse_Syntax_Base.range2))
                      (fun uu___ ->
                         (fun g1 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.If.fst"
                                          (Prims.of_int (231))
                                          (Prims.of_int (4))
                                          (Prims.of_int (231))
                                          (Prims.of_int (49)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.If.fst"
                                          (Prims.of_int (228))
                                          (Prims.of_int (64))
                                          (Prims.of_int (290))
                                          (Prims.of_int (43)))))
                                 (Obj.magic
                                    (Pulse_Checker_Pure.check_tot_term_with_expected_type
                                       g1 b Pulse_Typing.tm_bool))
                                 (fun uu___ ->
                                    (fun uu___ ->
                                       match uu___ with
                                       | Prims.Mkdtuple2 (b1, b_typing) ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (233))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (233))
                                                         (Prims.of_int (27)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (233))
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (290))
                                                         (Prims.of_int (43)))))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___1 ->
                                                      post_hint.Pulse_Typing.post))
                                                (fun uu___1 ->
                                                   (fun post ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (19)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (43)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___1 ->
                                                                 Pulse_Typing_Env.fresh
                                                                   g1))
                                                           (fun uu___1 ->
                                                              (fun hyp ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    fun eq_v
                                                                    ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 hyp
                                                                    (Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_if_hyp")
                                                                    (Pulse_Typing.mk_eq2
                                                                    Pulse_Syntax_Pure.u0
                                                                    Pulse_Typing.tm_bool
                                                                    b1 eq_v)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    g_with_eq
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    fun eq_v
                                                                    ->
                                                                    fun br ->
                                                                    fun
                                                                    is_then
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    g_with_eq
                                                                    eq_v))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    g_with_eq1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_if_br"))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    ppname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (check1
                                                                    g_with_eq1
                                                                    pre ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    ppname br))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g_with_eq1
                                                                    pre
                                                                    post_hint
                                                                    r ppname))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c,
                                                                    d) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    if
                                                                    is_then
                                                                    then
                                                                    "then"
                                                                    else
                                                                    "else"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    br_name
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    hyp
                                                                    (Pulse_Syntax_Naming.freevars_st
                                                                    br1)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (br1.Pulse_Syntax_Base.range2))
                                                                    (Prims.strcat
                                                                    "check_if: branch hypothesis is in freevars of checked "
                                                                    (Prims.strcat
                                                                    br_name
                                                                    " branch"))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c,
                                                                    d)))))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    check_branch
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    Pulse_Typing.tm_true
                                                                    e1 true))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e11, c1,
                                                                    e1_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    Pulse_Typing.tm_false
                                                                    e2 false))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e21, c2,
                                                                    e2_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (combine_if_branches
                                                                    (g_with_eq
                                                                    Pulse_Typing.tm_true)
                                                                    e11 c1
                                                                    e1_typing
                                                                    (g_with_eq
                                                                    Pulse_Typing.tm_false)
                                                                    e21 c2
                                                                    e2_typing))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c,
                                                                    e1_typing1,
                                                                    e2_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun x ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    post)
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Impossible: check_if: unexpected freevar in post, please file a bug-report")
                                                                    else
                                                                    if
                                                                    Prims.op_Negation
                                                                    (((Pulse_Syntax_Base.eq_tm
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c)
                                                                    post_hint.Pulse_Typing.ret_ty)
                                                                    &&
                                                                    (Pulse_Syntax_Base.eq_univ
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c)
                                                                    post_hint.Pulse_Typing.u))
                                                                    &&
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)
                                                                    post_hint.Pulse_Typing.post))
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (114)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    post_hint.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    post_hint.Pulse_Typing.ret_ty))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    fun x3 ->
                                                                    fun x4 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_if: computation type after combining branches does not match post hint,computed: ("
                                                                    (Prims.strcat
                                                                    (Pulse_Syntax_Printer.univ_to_string
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c)) ", "))
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    ", "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    "), expected ("))
                                                                    (Prims.strcat
                                                                    x2 ", "))
                                                                    (Prims.strcat
                                                                    x3 ", "))
                                                                    (Prims.strcat
                                                                    x4 ")")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8
                                                                    uu___7))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    (Pulse_Syntax_Printer.univ_to_string
                                                                    post_hint.Pulse_Typing.u)))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    uu___6))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6
                                                                    uu___5))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___5))
                                                                    uu___5))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.post_hint_typing
                                                                    g1
                                                                    post_hint
                                                                    x))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    post_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.intro_comp_typing
                                                                    g1 c ()
                                                                    () x ()))
                                                                    uu___6)))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    c
                                                                    (Pulse_Syntax_Base.Tm_If
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b1;
                                                                    Pulse_Syntax_Base.then_
                                                                    = e11;
                                                                    Pulse_Syntax_Base.else_
                                                                    = e21;
                                                                    Pulse_Syntax_Base.post1
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })), c,
                                                                    (Pulse_Typing.T_If
                                                                    (g1, b1,
                                                                    e11, e21,
                                                                    c,
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c), hyp,
                                                                    (),
                                                                    e1_typing1,
                                                                    e2_typing1,
                                                                    ())))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g1 pre
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    d
                                                                    res_ppname))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                uu___1)))
                                                     uu___1))) uu___))) uu___)