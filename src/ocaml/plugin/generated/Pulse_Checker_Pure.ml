open Prims
let (push_context :
  Prims.string ->
    Pulse_Syntax_Base.range -> Pulse_Typing_Env.env -> Pulse_Typing_Env.env)
  = fun ctx -> fun r -> fun g -> Pulse_Typing_Env.push_context g ctx r
let (debug :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun msg ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (19)) (Prims.of_int (22)) (Prims.of_int (19))
                 (Prims.of_int (36)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (20)) (Prims.of_int (2)) (Prims.of_int (21))
                 (Prims.of_int (47)))))
        (Obj.magic (FStar_Tactics_V2_Builtins.debugging ()))
        (fun uu___ ->
           (fun tac_debugging ->
              if
                tac_debugging ||
                  (Pulse_RuntimeUtils.debug_at_level
                     (Pulse_Typing_Env.fstar_env g) "refl_tc_callbacks")
              then
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (21)) (Prims.of_int (15))
                                 (Prims.of_int (21)) (Prims.of_int (47)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (21)) (Prims.of_int (7))
                                 (Prims.of_int (21)) (Prims.of_int (47)))))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (21))
                                       (Prims.of_int (16))
                                       (Prims.of_int (21))
                                       (Prims.of_int (31)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (21))
                                       (Prims.of_int (15))
                                       (Prims.of_int (21))
                                       (Prims.of_int (47)))))
                              (Obj.magic (Pulse_Typing_Env.print_context g))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (21))
                                                  (Prims.of_int (34))
                                                  (Prims.of_int (21))
                                                  (Prims.of_int (46)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "prims.fst"
                                                  (Prims.of_int (590))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (590))
                                                  (Prims.of_int (31)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (21))
                                                        (Prims.of_int (41))
                                                        (Prims.of_int (21))
                                                        (Prims.of_int (46)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (590))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (590))
                                                        (Prims.of_int (31)))))
                                               (Obj.magic (msg ()))
                                               (fun uu___1 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       Prims.strcat "\n"
                                                         uu___1))))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 Prims.strcat uu___ uu___1))))
                                   uu___)))
                        (fun uu___ ->
                           (fun uu___ ->
                              Obj.magic
                                (FStar_Tactics_V2_Builtins.print uu___))
                             uu___)))
              else
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
             uu___)
let (rtb_core_check_term :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        ((FStar_Reflection_Types.typ FStar_Pervasives_Native.option *
           FStar_Tactics_Types.issues),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (24)) (Prims.of_int (2)) (Prims.of_int (24))
                   (Prims.of_int (88)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (24)) (Prims.of_int (89))
                   (Prims.of_int (26)) (Prims.of_int (5)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (24)) (Prims.of_int (67))
                              (Prims.of_int (24)) (Prims.of_int (87)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string e))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             Prims.strcat "Calling core_check_term on "
                               (Prims.strcat uu___1 ""))))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (25)) (Prims.of_int (12))
                              (Prims.of_int (25)) (Prims.of_int (50)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (25)) (Prims.of_int (6))
                              (Prims.of_int (25)) (Prims.of_int (9)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Builtins.core_compute_term_type f e
                           FStar_Tactics_Types.E_Total))
                     (fun res ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> res))))
               uu___)
let (rtb_tc_term :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((FStar_Reflection_Types.term * FStar_Reflection_Types.typ)
           FStar_Pervasives_Native.option * FStar_Tactics_Types.issues),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (29)) (Prims.of_int (2)) (Prims.of_int (29))
                   (Prims.of_int (80)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (29)) (Prims.of_int (81))
                   (Prims.of_int (31)) (Prims.of_int (5)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (29)) (Prims.of_int (59))
                              (Prims.of_int (29)) (Prims.of_int (79)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string e))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             Prims.strcat "Calling tc_term on "
                               (Prims.strcat uu___1 ""))))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (30)) (Prims.of_int (12))
                              (Prims.of_int (30)) (Prims.of_int (35)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (30)) (Prims.of_int (6))
                              (Prims.of_int (30)) (Prims.of_int (9)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Builtins.tc_term f e
                           FStar_Tactics_Types.E_Total))
                     (fun res ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> res))))
               uu___)
let (rtb_universe_of :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        ((FStar_Reflection_Types.universe FStar_Pervasives_Native.option *
           FStar_Tactics_Types.issues),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (34)) (Prims.of_int (2)) (Prims.of_int (34))
                   (Prims.of_int (84)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (34)) (Prims.of_int (85))
                   (Prims.of_int (36)) (Prims.of_int (5)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (34)) (Prims.of_int (63))
                              (Prims.of_int (34)) (Prims.of_int (83)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string e))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             Prims.strcat "Calling universe_of on "
                               (Prims.strcat uu___1 ""))))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (35)) (Prims.of_int (12))
                              (Prims.of_int (35)) (Prims.of_int (31)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (35)) (Prims.of_int (6))
                              (Prims.of_int (35)) (Prims.of_int (9)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.universe_of f e))
                     (fun res ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> res))))
               uu___)
let (rtb_check_subtyping :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (((unit, unit, unit) FStar_Tactics_Types.subtyping_token
             FStar_Pervasives_Native.option * FStar_Tactics_Types.issues),
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun t1 ->
        fun t2 ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (39)) (Prims.of_int (2))
                     (Prims.of_int (41)) (Prims.of_int (61)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (41)) (Prims.of_int (62))
                     (Prims.of_int (43)) (Prims.of_int (5)))))
            (Obj.magic
               (debug g
                  (fun uu___ ->
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (41)) (Prims.of_int (39))
                                (Prims.of_int (41)) (Prims.of_int (60)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (39)) (Prims.of_int (20))
                                (Prims.of_int (41)) (Prims.of_int (60)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Builtins.term_to_string t2))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (39))
                                           (Prims.of_int (20))
                                           (Prims.of_int (41))
                                           (Prims.of_int (60)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (39))
                                           (Prims.of_int (20))
                                           (Prims.of_int (41))
                                           (Prims.of_int (60)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Pure.fst"
                                                 (Prims.of_int (40))
                                                 (Prims.of_int (39))
                                                 (Prims.of_int (40))
                                                 (Prims.of_int (60)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Printf.fst"
                                                 (Prims.of_int (121))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (123))
                                                 (Prims.of_int (44)))))
                                        (Obj.magic
                                           (FStar_Tactics_V2_Builtins.term_to_string
                                              t1))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                fun x ->
                                                  Prims.strcat
                                                    (Prims.strcat
                                                       "Calling check_subtyping on "
                                                       (Prims.strcat uu___2
                                                          " <: "))
                                                    (Prims.strcat x "")))))
                                  (fun uu___2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 -> uu___2 uu___1))))
                            uu___1))))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (42)) (Prims.of_int (12))
                                (Prims.of_int (42)) (Prims.of_int (39)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (42)) (Prims.of_int (6))
                                (Prims.of_int (42)) (Prims.of_int (9)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Builtins.check_subtyping f t1 t2))
                       (fun res ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> res)))) uu___)
let (rtb_instantiate_implicits :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((FStar_Reflection_Types.term * FStar_Reflection_Types.typ)
           FStar_Pervasives_Native.option * FStar_Tactics_Types.issues),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (46)) (Prims.of_int (2)) (Prims.of_int (47))
                   (Prims.of_int (60)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (47)) (Prims.of_int (61))
                   (Prims.of_int (50)) (Prims.of_int (5)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (47)) (Prims.of_int (39))
                              (Prims.of_int (47)) (Prims.of_int (59)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string t))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             Prims.strcat "Calling instantiate_implicits on "
                               (Prims.strcat uu___1 ""))))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (48)) (Prims.of_int (12))
                              (Prims.of_int (48)) (Prims.of_int (41)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (49)) (Prims.of_int (2))
                              (Prims.of_int (50)) (Prims.of_int (5)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Builtins.instantiate_implicits f t))
                     (fun uu___1 ->
                        (fun res ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (49))
                                         (Prims.of_int (2))
                                         (Prims.of_int (49))
                                         (Prims.of_int (58)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (48))
                                         (Prims.of_int (6))
                                         (Prims.of_int (48))
                                         (Prims.of_int (9)))))
                                (Obj.magic
                                   (debug g
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    "Returned from instantiate_implicits")))
                                           uu___1)))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> res)))) uu___1))) uu___)
let (rtb_core_check_term_at_type :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (((unit, unit, unit) FStar_Tactics_Types.typing_token
             FStar_Pervasives_Native.option * FStar_Tactics_Types.issues),
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        fun t ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (53)) (Prims.of_int (2))
                     (Prims.of_int (55)) (Prims.of_int (60)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (55)) (Prims.of_int (61))
                     (Prims.of_int (57)) (Prims.of_int (5)))))
            (Obj.magic
               (debug g
                  (fun uu___ ->
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (55)) (Prims.of_int (39))
                                (Prims.of_int (55)) (Prims.of_int (59)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (53)) (Prims.of_int (20))
                                (Prims.of_int (55)) (Prims.of_int (59)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Builtins.term_to_string t))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (53))
                                           (Prims.of_int (20))
                                           (Prims.of_int (55))
                                           (Prims.of_int (59)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (53))
                                           (Prims.of_int (20))
                                           (Prims.of_int (55))
                                           (Prims.of_int (59)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Pure.fst"
                                                 (Prims.of_int (54))
                                                 (Prims.of_int (39))
                                                 (Prims.of_int (54))
                                                 (Prims.of_int (59)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Printf.fst"
                                                 (Prims.of_int (121))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (123))
                                                 (Prims.of_int (44)))))
                                        (Obj.magic
                                           (FStar_Tactics_V2_Builtins.term_to_string
                                              e))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                fun x ->
                                                  Prims.strcat
                                                    (Prims.strcat
                                                       "Calling core_check_term on "
                                                       (Prims.strcat uu___2
                                                          " and "))
                                                    (Prims.strcat x "")))))
                                  (fun uu___2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 -> uu___2 uu___1))))
                            uu___1))))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (56)) (Prims.of_int (12))
                                (Prims.of_int (56)) (Prims.of_int (47)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (56)) (Prims.of_int (6))
                                (Prims.of_int (56)) (Prims.of_int (9)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Builtins.core_check_term f e t
                             FStar_Tactics_Types.E_Total))
                       (fun res ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> res)))) uu___)
let (mk_squash : FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t ->
    let sq =
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_UInst
           ((FStar_Reflection_V2_Builtins.pack_fv
               FStar_Reflection_Const.squash_qn), [Pulse_Syntax_Pure.u_zero])) in
    FStar_Reflection_V2_Derived.mk_e_app sq [t]
let (squash_prop_validity_token :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (unit, unit) FStar_Tactics_V2_Builtins.prop_validity_token ->
        (unit, unit) FStar_Tactics_V2_Builtins.prop_validity_token)
  = fun f -> fun p -> fun t -> t
let (rtb_check_prop_validity :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((unit, unit) FStar_Tactics_V2_Builtins.prop_validity_token
           FStar_Pervasives_Native.option * FStar_Tactics_Types.issues),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun p ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (68)) (Prims.of_int (2)) (Prims.of_int (69))
                   (Prims.of_int (60)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (69)) (Prims.of_int (61))
                   (Prims.of_int (74)) (Prims.of_int (65)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (69)) (Prims.of_int (39))
                              (Prims.of_int (69)) (Prims.of_int (59)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string p))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             Prims.strcat "Calling check_prop_validity on "
                               (Prims.strcat uu___1 ""))))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (70)) (Prims.of_int (11))
                              (Prims.of_int (70)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (70)) (Prims.of_int (25))
                              (Prims.of_int (74)) (Prims.of_int (65)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> mk_squash p))
                     (fun uu___1 ->
                        (fun sp ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (71))
                                         (Prims.of_int (20))
                                         (Prims.of_int (71))
                                         (Prims.of_int (48)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (70))
                                         (Prims.of_int (25))
                                         (Prims.of_int (74))
                                         (Prims.of_int (65)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Builtins.check_prop_validity
                                      f sp))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        match uu___1 with
                                        | (res, issues) ->
                                            (match res with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 (FStar_Pervasives_Native.None,
                                                   issues)
                                             | FStar_Pervasives_Native.Some
                                                 tok ->
                                                 ((FStar_Pervasives_Native.Some
                                                     (squash_prop_validity_token
                                                        f p tok)), issues))))))
                          uu___1))) uu___)
let (exn_as_issue : Prims.exn -> FStar_Issue.issue) =
  fun e ->
    FStar_Issue.mk_issue "Error" (Pulse_RuntimeUtils.print_exn e)
      FStar_Pervasives_Native.None FStar_Pervasives_Native.None []
let catch_all :
  'a .
    (unit ->
       (('a FStar_Pervasives_Native.option * FStar_Tactics_Types.issues),
         unit) FStar_Tactics_Effect.tac_repr)
      ->
      (('a FStar_Pervasives_Native.option * FStar_Tactics_Types.issues),
        unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (81)) (Prims.of_int (10)) (Prims.of_int (81))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (81)) (Prims.of_int (4)) (Prims.of_int (84))
               (Prims.of_int (16)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.catch f))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | FStar_Pervasives.Inl exn ->
                  (FStar_Pervasives_Native.None, [exn_as_issue exn])
              | FStar_Pervasives.Inr v -> v))
let (readback_failure :
  FStar_Reflection_Types.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (88)) (Prims.of_int (17)) (Prims.of_int (88))
               (Prims.of_int (37)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
               (Prims.of_int (19)) (Prims.of_int (590)) (Prims.of_int (31)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string s))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              Prims.strcat "Internal error: failed to readback F* term "
                (Prims.strcat uu___ "")))
let (ill_typed_term :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
        (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun expected_typ ->
      fun got_typ ->
        match (expected_typ, got_typ) with
        | (FStar_Pervasives_Native.None, uu___) ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (93)) (Prims.of_int (40))
                       (Prims.of_int (93)) (Prims.of_int (60)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                       (Prims.of_int (19)) (Prims.of_int (590))
                       (Prims.of_int (31)))))
              (Obj.magic (Pulse_Syntax_Printer.term_to_string t))
              (fun uu___1 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      Prims.strcat "Ill-typed term: "
                        (Prims.strcat uu___1 "")))
        | (FStar_Pervasives_Native.Some ty, FStar_Pervasives_Native.None) ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (95)) (Prims.of_int (76))
                       (Prims.of_int (95)) (Prims.of_int (96)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (95)) (Prims.of_int (4))
                       (Prims.of_int (95)) (Prims.of_int (96)))))
              (Obj.magic (Pulse_Syntax_Printer.term_to_string t))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (95)) (Prims.of_int (4))
                                  (Prims.of_int (95)) (Prims.of_int (96)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (95)) (Prims.of_int (4))
                                  (Prims.of_int (95)) (Prims.of_int (96)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Pure.fst"
                                        (Prims.of_int (95))
                                        (Prims.of_int (54))
                                        (Prims.of_int (95))
                                        (Prims.of_int (75)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "FStar.Printf.fst"
                                        (Prims.of_int (121))
                                        (Prims.of_int (8))
                                        (Prims.of_int (123))
                                        (Prims.of_int (44)))))
                               (Obj.magic
                                  (Pulse_Syntax_Printer.term_to_string ty))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       fun x ->
                                         Prims.strcat
                                           (Prims.strcat
                                              "Expected term of type "
                                              (Prims.strcat uu___1 "; got "))
                                           (Prims.strcat x "")))))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 -> uu___1 uu___)))) uu___)
        | (FStar_Pervasives_Native.Some ty, FStar_Pervasives_Native.Some ty')
            ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (100)) (Prims.of_int (19))
                       (Prims.of_int (100)) (Prims.of_int (41)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (97)) (Prims.of_int (4))
                       (Prims.of_int (100)) (Prims.of_int (41)))))
              (Obj.magic (Pulse_Syntax_Printer.term_to_string ty'))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (97)) (Prims.of_int (4))
                                  (Prims.of_int (100)) (Prims.of_int (41)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (97)) (Prims.of_int (4))
                                  (Prims.of_int (100)) (Prims.of_int (41)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Pure.fst"
                                        (Prims.of_int (99))
                                        (Prims.of_int (19))
                                        (Prims.of_int (99))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Pure.fst"
                                        (Prims.of_int (97))
                                        (Prims.of_int (4))
                                        (Prims.of_int (100))
                                        (Prims.of_int (41)))))
                               (Obj.magic
                                  (Pulse_Syntax_Printer.term_to_string t))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Pure.fst"
                                                   (Prims.of_int (97))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (100))
                                                   (Prims.of_int (41)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Pure.fst"
                                                   (Prims.of_int (97))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (100))
                                                   (Prims.of_int (41)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Pure.fst"
                                                         (Prims.of_int (98))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (98))
                                                         (Prims.of_int (40)))))
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
                                                      ty))
                                                (fun uu___2 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        fun x ->
                                                          fun x1 ->
                                                            Prims.strcat
                                                              (Prims.strcat
                                                                 (Prims.strcat
                                                                    "Expected term of type "
                                                                    (
                                                                    Prims.strcat
                                                                    uu___2
                                                                    "; got "))
                                                                 (Prims.strcat
                                                                    x
                                                                    " of type "))
                                                              (Prims.strcat
                                                                 x1 "")))))
                                          (fun uu___2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 -> uu___2 uu___1))))
                                    uu___1)))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 -> uu___1 uu___)))) uu___)
let (instantiate_term_implicits :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term * Pulse_Syntax_Base.term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (103)) (Prims.of_int (10))
                 (Prims.of_int (103)) (Prims.of_int (20)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (103)) (Prims.of_int (23))
                 (Prims.of_int (120)) (Prims.of_int (49)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun f ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (104)) (Prims.of_int (11))
                            (Prims.of_int (104)) (Prims.of_int (23)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (104)) (Prims.of_int (26))
                            (Prims.of_int (120)) (Prims.of_int (49)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Elaborate_Pure.elab_term t0))
                   (fun uu___ ->
                      (fun rt ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (105))
                                       (Prims.of_int (21))
                                       (Prims.of_int (105))
                                       (Prims.of_int (74)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (104))
                                       (Prims.of_int (26))
                                       (Prims.of_int (120))
                                       (Prims.of_int (49)))))
                              (Obj.magic
                                 (catch_all
                                    (fun uu___ ->
                                       rtb_instantiate_implicits g f rt)))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    match uu___ with
                                    | (topt, issues) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (106))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (106))
                                                      (Prims.of_int (33)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (107))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (120))
                                                      (Prims.of_int (49)))))
                                             (Obj.magic
                                                (FStar_Tactics_V1_Builtins.log_issues
                                                   issues))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match topt with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (45)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (45)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (44)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                  (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    t0))
                                                                  (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Could not infer implicit arguments in "
                                                                    (Prims.strcat
                                                                    uu___2 "")))))
                                                            (fun uu___2 ->
                                                               (fun uu___2 ->
                                                                  Obj.magic
                                                                    (
                                                                    Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t0.Pulse_Syntax_Base.range1))
                                                                    uu___2))
                                                                 uu___2))
                                                   | FStar_Pervasives_Native.Some
                                                       (t, ty) ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (28)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (49)))))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  Pulse_Readback.readback_ty
                                                                    t))
                                                            (fun uu___2 ->
                                                               (fun topt1 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Readback.readback_ty
                                                                    ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    tyopt ->
                                                                    match 
                                                                    (topt1,
                                                                    tyopt)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    t1,
                                                                    FStar_Pervasives_Native.Some
                                                                    ty1) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (t1, ty1))))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    uu___2,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (readback_failure
                                                                    ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t0.Pulse_Syntax_Base.range1))
                                                                    uu___3))
                                                                    uu___3)))
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    uu___2)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (readback_failure
                                                                    t))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t0.Pulse_Syntax_Base.range1))
                                                                    uu___3))
                                                                    uu___3))))
                                                                    uu___2)))
                                                                 uu___2)))
                                                  uu___1))) uu___))) uu___)))
             uu___)
let (check_universe :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.universe, unit) Prims.dtuple2, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (124)) (Prims.of_int (12))
                 (Prims.of_int (124)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (124)) (Prims.of_int (25))
                 (Prims.of_int (137)) (Prims.of_int (23)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun f ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (125)) (Prims.of_int (13))
                            (Prims.of_int (125)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (125)) (Prims.of_int (27))
                            (Prims.of_int (137)) (Prims.of_int (23)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                   (fun uu___ ->
                      (fun rt ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (126))
                                       (Prims.of_int (25))
                                       (Prims.of_int (126))
                                       (Prims.of_int (68)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (125))
                                       (Prims.of_int (27))
                                       (Prims.of_int (137))
                                       (Prims.of_int (23)))))
                              (Obj.magic
                                 (catch_all
                                    (fun uu___ -> rtb_universe_of g f rt)))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    match uu___ with
                                    | (ru_opt, issues) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (127))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (127))
                                                      (Prims.of_int (23)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (128))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (137))
                                                      (Prims.of_int (23)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Builtins.log_issues
                                                   issues))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match ru_opt with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (78)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (78)))))
                                                               (Obj.magic
                                                                  (ill_typed_term
                                                                    t
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Pure.tm_type
                                                                    Pulse_Syntax_Pure.u_unknown))
                                                                    FStar_Pervasives_Native.None))
                                                               (fun uu___2 ->
                                                                  (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___2))
                                                                    uu___2)))
                                                   | FStar_Pervasives_Native.Some
                                                       ru ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  Prims.Mkdtuple2
                                                                    (ru, ())))))
                                                  uu___1))) uu___))) uu___)))
             uu___)
let (tc_meta_callback :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((FStar_Reflection_Types.term, FStar_Reflection_Types.term,
           (unit, unit, unit) FStar_Reflection_Typing.tot_typing)
           FStar_Pervasives.dtuple3 FStar_Pervasives_Native.option *
           FStar_Tactics_Types.issues),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (143)) (Prims.of_int (6))
                   (Prims.of_int (148)) (Prims.of_int (14)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (142)) (Prims.of_int (8))
                   (Prims.of_int (142)) (Prims.of_int (11)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (143)) (Prims.of_int (12))
                         (Prims.of_int (143)) (Prims.of_int (50)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (143)) (Prims.of_int (6))
                         (Prims.of_int (148)) (Prims.of_int (14)))))
                (Obj.magic (catch_all (fun uu___ -> rtb_tc_term g f e)))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        match uu___ with
                        | (FStar_Pervasives_Native.None, issues) ->
                            (FStar_Pervasives_Native.None, issues)
                        | (FStar_Pervasives_Native.Some (e1, t), issues) ->
                            ((FStar_Pervasives_Native.Some
                                (FStar_Pervasives.Mkdtuple3
                                   (e1, t,
                                     (FStar_Reflection_Typing.T_Token
                                        (f, e1,
                                          (FStar_Tactics_Types.E_Total, t),
                                          ()))))), issues)))))
          (fun res -> FStar_Tactics_Effect.lift_div_tac (fun uu___ -> res))
let (check_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, Pulse_Syntax_Base.term,
         (unit, unit, unit) Pulse_Typing.typing) FStar_Pervasives.dtuple3,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (156)) (Prims.of_int (13))
                 (Prims.of_int (156)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (156)) (Prims.of_int (26))
                 (Prims.of_int (171)) (Prims.of_int (43)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun fg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (157)) (Prims.of_int (13))
                            (Prims.of_int (157)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (158)) (Prims.of_int (4))
                            (Prims.of_int (171)) (Prims.of_int (43)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                   (fun uu___ ->
                      (fun rt ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (158))
                                       (Prims.of_int (4))
                                       (Prims.of_int (161))
                                       (Prims.of_int (44)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (161))
                                       (Prims.of_int (45))
                                       (Prims.of_int (171))
                                       (Prims.of_int (43)))))
                              (Obj.magic
                                 (debug g
                                    (fun uu___ ->
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (161))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (161))
                                                  (Prims.of_int (43)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (159))
                                                  (Prims.of_int (12))
                                                  (Prims.of_int (161))
                                                  (Prims.of_int (43)))))
                                         (Obj.magic
                                            (FStar_Tactics_V2_Builtins.term_to_string
                                               rt))
                                         (fun uu___1 ->
                                            (fun uu___1 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (159))
                                                             (Prims.of_int (12))
                                                             (Prims.of_int (161))
                                                             (Prims.of_int (43)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (159))
                                                             (Prims.of_int (12))
                                                             (Prims.of_int (161))
                                                             (Prims.of_int (43)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (160))
                                                                   (Prims.of_int (22))
                                                                   (Prims.of_int (160))
                                                                   (Prims.of_int (42)))))
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
                                                                t))
                                                          (fun uu___2 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___3 ->
                                                                  fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_tot : called on "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " elaborated to "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            uu___2 uu___1))))
                                              uu___1))))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (162))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (162))
                                                  (Prims.of_int (46)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (161))
                                                  (Prims.of_int (45))
                                                  (Prims.of_int (171))
                                                  (Prims.of_int (43)))))
                                         (Obj.magic
                                            (tc_meta_callback g fg rt))
                                         (fun uu___1 ->
                                            (fun uu___1 ->
                                               match uu___1 with
                                               | (res, issues) ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Pure.fst"
                                                                 (Prims.of_int (163))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (163))
                                                                 (Prims.of_int (23)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Pure.fst"
                                                                 (Prims.of_int (164))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (171))
                                                                 (Prims.of_int (43)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Builtins.log_issues
                                                              issues))
                                                        (fun uu___2 ->
                                                           (fun uu___2 ->
                                                              match res with
                                                              | FStar_Pervasives_Native.None
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (ill_typed_term
                                                                    t
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___3))
                                                                    uu___3)))
                                                              | FStar_Pervasives_Native.Some
                                                                  (FStar_Pervasives.Mkdtuple3
                                                                  (rt1, ty',
                                                                   tok))
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (match 
                                                                    ((Pulse_Readback.readback_ty
                                                                    rt1),
                                                                    (Pulse_Readback.readback_ty
                                                                    ty'))
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    uu___3)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    (readback_failure
                                                                    rt1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___4))
                                                                    uu___4))
                                                                    | 
                                                                    (uu___3,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (readback_failure
                                                                    ty'))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___4))
                                                                    uu___4))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    t1,
                                                                    FStar_Pervasives_Native.Some
                                                                    ty) ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t1, ty,
                                                                    tok))))))
                                                             uu___2))) uu___1)))
                                   uu___))) uu___))) uu___)
let (check_term_and_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, Pulse_Syntax_Base.universe,
         Pulse_Syntax_Base.term, unit,
         (unit, unit, unit) Pulse_Typing.typing) FStar_Pervasives.dtuple5,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (180)) (Prims.of_int (13))
                 (Prims.of_int (180)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (180)) (Prims.of_int (26))
                 (Prims.of_int (193)) (Prims.of_int (32)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun fg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (181)) (Prims.of_int (13))
                            (Prims.of_int (181)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (181)) (Prims.of_int (27))
                            (Prims.of_int (193)) (Prims.of_int (32)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                   (fun uu___ ->
                      (fun rt ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (182))
                                       (Prims.of_int (22))
                                       (Prims.of_int (182))
                                       (Prims.of_int (46)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (181))
                                       (Prims.of_int (27))
                                       (Prims.of_int (193))
                                       (Prims.of_int (32)))))
                              (Obj.magic (tc_meta_callback g fg rt))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    match uu___ with
                                    | (res, issues) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (183))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (183))
                                                      (Prims.of_int (23)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (184))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (193))
                                                      (Prims.of_int (32)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Builtins.log_issues
                                                   issues))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match res with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (56)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (56)))))
                                                            (Obj.magic
                                                               (ill_typed_term
                                                                  t
                                                                  FStar_Pervasives_Native.None
                                                                  FStar_Pervasives_Native.None))
                                                            (fun uu___2 ->
                                                               (fun uu___2 ->
                                                                  Obj.magic
                                                                    (
                                                                    Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___2))
                                                                 uu___2))
                                                   | FStar_Pervasives_Native.Some
                                                       (FStar_Pervasives.Mkdtuple3
                                                       (rt1, ty', tok)) ->
                                                       (match ((Pulse_Readback.readback_ty
                                                                  rt1),
                                                                (Pulse_Readback.readback_ty
                                                                   ty'))
                                                        with
                                                        | (FStar_Pervasives_Native.None,
                                                           uu___2) ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (62)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (62)))))
                                                                 (Obj.magic
                                                                    (
                                                                    readback_failure
                                                                    rt1))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___3))
                                                                    uu___3))
                                                        | (uu___2,
                                                           FStar_Pervasives_Native.None)
                                                            ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (63)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (63)))))
                                                                 (Obj.magic
                                                                    (
                                                                    readback_failure
                                                                    ty'))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___3))
                                                                    uu___3))
                                                        | (FStar_Pervasives_Native.Some
                                                           t1,
                                                           FStar_Pervasives_Native.Some
                                                           ty) ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (46)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (32)))))
                                                                 (Obj.magic
                                                                    (
                                                                    check_universe
                                                                    g ty))
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u, uty)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (t1, u,
                                                                    ty, (),
                                                                    tok))))))
                                                  uu___1))) uu___))) uu___)))
             uu___)
let (check_term_with_expected_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        ((Pulse_Syntax_Base.term, (unit, unit, unit) Pulse_Typing.typing)
           Prims.dtuple2,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (199)) (Prims.of_int (13))
                   (Prims.of_int (199)) (Prims.of_int (43)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (197)) (Prims.of_int (35))
                   (Prims.of_int (214)) (Prims.of_int (74)))))
          (Obj.magic (instantiate_term_implicits g e))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | (e1, uu___1) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (201)) (Prims.of_int (11))
                                  (Prims.of_int (201)) (Prims.of_int (21)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (201)) (Prims.of_int (24))
                                  (Prims.of_int (214)) (Prims.of_int (74)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> Pulse_Typing.elab_env g))
                         (fun uu___2 ->
                            (fun fg ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (202))
                                             (Prims.of_int (11))
                                             (Prims.of_int (202))
                                             (Prims.of_int (22)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (202))
                                             (Prims.of_int (25))
                                             (Prims.of_int (214))
                                             (Prims.of_int (74)))))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          Pulse_Elaborate_Pure.elab_term e1))
                                    (fun uu___2 ->
                                       (fun re ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (203))
                                                        (Prims.of_int (11))
                                                        (Prims.of_int (203))
                                                        (Prims.of_int (22)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (203))
                                                        (Prims.of_int (25))
                                                        (Prims.of_int (214))
                                                        (Prims.of_int (74)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     Pulse_Elaborate_Pure.elab_term
                                                       t))
                                               (fun uu___2 ->
                                                  (fun rt ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (206))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (209))
                                                                   (Prims.of_int (16)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (203))
                                                                   (Prims.of_int (25))
                                                                   (Prims.of_int (214))
                                                                   (Prims.of_int (74)))))
                                                          (Obj.magic
                                                             (catch_all
                                                                (fun uu___2
                                                                   ->
                                                                   rtb_core_check_term_at_type
                                                                    (Pulse_Typing_Env.push_context
                                                                    g
                                                                    "check_term_with_expected_type"
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    rt)) fg
                                                                    re rt)))
                                                          (fun uu___2 ->
                                                             (fun uu___2 ->
                                                                match uu___2
                                                                with
                                                                | (topt,
                                                                   issues) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.log_issues
                                                                    issues))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match topt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (ill_typed_term
                                                                    e1
                                                                    (FStar_Pervasives_Native.Some
                                                                    t)
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e1.Pulse_Syntax_Base.range1))
                                                                    uu___4))
                                                                    uu___4)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tok ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.Mkdtuple2
                                                                    (e1,
                                                                    (FStar_Reflection_Typing.T_Token
                                                                    (fg, re,
                                                                    (FStar_Tactics_Types.E_Total,
                                                                    rt), ())))))))
                                                                    uu___3)))
                                                               uu___2)))
                                                    uu___2))) uu___2)))
                              uu___2))) uu___)
let (tc_with_core :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((FStar_Reflection_Types.term,
           (unit, unit, unit) FStar_Reflection_Typing.tot_typing)
           Prims.dtuple2 FStar_Pervasives_Native.option *
           FStar_Tactics_Types.issues),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (218)) (Prims.of_int (23))
                   (Prims.of_int (218)) (Prims.of_int (117)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (218)) (Prims.of_int (3))
                   (Prims.of_int (222)) (Prims.of_int (71)))))
          (Obj.magic
             (catch_all
                (fun uu___ ->
                   rtb_core_check_term
                     (Pulse_Typing_Env.push_context g "tc_with_core"
                        (FStar_Reflection_V2_Builtins.range_of_term e)) f e)))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  match uu___ with
                  | (ropt, issues) ->
                      (match ropt with
                       | FStar_Pervasives_Native.None ->
                           (FStar_Pervasives_Native.None, issues)
                       | FStar_Pervasives_Native.Some t ->
                           ((FStar_Pervasives_Native.Some
                               (Prims.Mkdtuple2
                                  (t,
                                    (FStar_Reflection_Typing.T_Token
                                       (f, e,
                                         (FStar_Tactics_Types.E_Total, t),
                                         ()))))), issues))))
let (core_check_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, (unit, unit, unit) Pulse_Typing.typing)
         Prims.dtuple2,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (227)) (Prims.of_int (13))
                 (Prims.of_int (227)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (227)) (Prims.of_int (26))
                 (Prims.of_int (239)) (Prims.of_int (23)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun fg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (228)) (Prims.of_int (13))
                            (Prims.of_int (228)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (228)) (Prims.of_int (27))
                            (Prims.of_int (239)) (Prims.of_int (23)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                   (fun uu___ ->
                      (fun rt ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (229))
                                       (Prims.of_int (22))
                                       (Prims.of_int (229))
                                       (Prims.of_int (94)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (228))
                                       (Prims.of_int (27))
                                       (Prims.of_int (239))
                                       (Prims.of_int (23)))))
                              (Obj.magic
                                 (tc_with_core
                                    (Pulse_Typing_Env.push_context g
                                       "core_check_term"
                                       (FStar_Reflection_V2_Builtins.range_of_term
                                          rt)) fg rt))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    match uu___ with
                                    | (res, issues) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (230))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (230))
                                                      (Prims.of_int (23)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (231))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (239))
                                                      (Prims.of_int (23)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Builtins.log_issues
                                                   issues))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match res with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (56)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (56)))))
                                                               (Obj.magic
                                                                  (ill_typed_term
                                                                    t
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Pervasives_Native.None))
                                                               (fun uu___2 ->
                                                                  (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___2))
                                                                    uu___2)))
                                                   | FStar_Pervasives_Native.Some
                                                       (Prims.Mkdtuple2
                                                       (ty', tok)) ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (match Pulse_Readback.readback_ty
                                                                    ty'
                                                             with
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 Obj.repr
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (readback_failure
                                                                    ty'))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___2))
                                                                    uu___2))
                                                             | FStar_Pervasives_Native.Some
                                                                 ty ->
                                                                 Obj.repr
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.Mkdtuple2
                                                                    (ty, tok))))))
                                                  uu___1))) uu___))) uu___)))
             uu___)
let (core_check_term_with_expected_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        ((unit, unit, unit) Pulse_Typing.typing, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (242)) (Prims.of_int (11))
                   (Prims.of_int (242)) (Prims.of_int (21)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (242)) (Prims.of_int (24))
                   (Prims.of_int (254)) (Prims.of_int (65)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Typing.elab_env g))
          (fun uu___ ->
             (fun fg ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (243)) (Prims.of_int (11))
                              (Prims.of_int (243)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (243)) (Prims.of_int (25))
                              (Prims.of_int (254)) (Prims.of_int (65)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Pulse_Elaborate_Pure.elab_term e))
                     (fun uu___ ->
                        (fun re ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (244))
                                         (Prims.of_int (11))
                                         (Prims.of_int (244))
                                         (Prims.of_int (22)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (244))
                                         (Prims.of_int (25))
                                         (Prims.of_int (254))
                                         (Prims.of_int (65)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      Pulse_Elaborate_Pure.elab_term t))
                                (fun uu___ ->
                                   (fun rt ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (246))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (249))
                                                    (Prims.of_int (16)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (244))
                                                    (Prims.of_int (25))
                                                    (Prims.of_int (254))
                                                    (Prims.of_int (65)))))
                                           (Obj.magic
                                              (catch_all
                                                 (fun uu___ ->
                                                    rtb_core_check_term_at_type
                                                      (Pulse_Typing_Env.push_context
                                                         g
                                                         "core_check_term_with_expected_type"
                                                         (FStar_Reflection_V2_Builtins.range_of_term
                                                            rt)) fg re rt)))
                                           (fun uu___ ->
                                              (fun uu___ ->
                                                 match uu___ with
                                                 | (topt, issues) ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (250))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (250))
                                                                   (Prims.of_int (21)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (251))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (254))
                                                                   (Prims.of_int (65)))))
                                                          (Obj.magic
                                                             (FStar_Tactics_V2_Builtins.log_issues
                                                                issues))
                                                          (fun uu___1 ->
                                                             (fun uu___1 ->
                                                                match topt
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (ill_typed_term
                                                                    e
                                                                    (FStar_Pervasives_Native.Some
                                                                    t)
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e.Pulse_Syntax_Base.range1))
                                                                    uu___2))
                                                                    uu___2)))
                                                                | FStar_Pervasives_Native.Some
                                                                    tok ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Reflection_Typing.T_Token
                                                                    ((Pulse_Typing.elab_env
                                                                    g),
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    e),
                                                                    (FStar_Tactics_Types.E_Total,
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    t)), ())))))
                                                               uu___1)))
                                                uu___))) uu___))) uu___)))
               uu___)
let (check_vprop :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, unit) Prims.dtuple2, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (260)) (Prims.of_int (4)) (Prims.of_int (260))
                 (Prims.of_int (84)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (258)) (Prims.of_int (46))
                 (Prims.of_int (261)) (Prims.of_int (21)))))
        (Obj.magic
           (check_term_with_expected_type
              (Pulse_Typing_Env.push_context_no_range g "check_vprop") t
              Pulse_Syntax_Base.tm_vprop))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                match uu___ with
                | Prims.Mkdtuple2 (t1, t_typing) -> Prims.Mkdtuple2 (t1, ())))
let (check_vprop_with_core :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (268)) (Prims.of_int (17))
                 (Prims.of_int (268)) (Prims.of_int (112)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (269)) (Prims.of_int (2)) (Prims.of_int (269))
                 (Prims.of_int (12)))))
        (Obj.magic
           (core_check_term_with_expected_type
              (Pulse_Typing_Env.push_context_no_range g
                 "check_vprop_with_core") t Pulse_Syntax_Base.tm_vprop))
        (fun t_typing -> FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))
let (get_non_informative_witness :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        ((unit, unit, unit) Pulse_Typing.non_informative_t, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun u ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (274)) (Prims.of_int (6))
                   (Prims.of_int (276)) (Prims.of_int (52)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (276)) (Prims.of_int (55))
                   (Prims.of_int (303)) (Prims.of_int (16)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun uu___1 ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (275)) (Prims.of_int (13))
                             (Prims.of_int (276)) (Prims.of_int (52)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (274)) (Prims.of_int (6))
                             (Prims.of_int (276)) (Prims.of_int (52)))))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (276)) (Prims.of_int (31))
                                   (Prims.of_int (276)) (Prims.of_int (51)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "prims.fst"
                                   (Prims.of_int (590)) (Prims.of_int (19))
                                   (Prims.of_int (590)) (Prims.of_int (31)))))
                          (Obj.magic (Pulse_Syntax_Printer.term_to_string t))
                          (fun uu___2 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  Prims.strcat
                                    "Expected a term with a non-informative (e.g., erased) type; got  "
                                    (Prims.strcat uu___2 "")))))
                    (fun uu___2 ->
                       (fun uu___2 ->
                          Obj.magic
                            (Pulse_Typing_Env.fail g
                               (FStar_Pervasives_Native.Some
                                  (t.Pulse_Syntax_Base.range1)) uu___2))
                         uu___2)))
          (fun uu___ ->
             (fun err ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (277)) (Prims.of_int (14))
                              (Prims.of_int (296)) (Prims.of_int (17)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (298)) (Prims.of_int (4))
                              (Prims.of_int (303)) (Prims.of_int (16)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           match Pulse_Syntax_Pure.is_fvar_app t with
                           | FStar_Pervasives_Native.Some
                               (l, us, uu___1, arg_opt) ->
                               if l = FStar_Reflection_Const.unit_lid
                               then
                                 FStar_Pervasives_Native.Some
                                   (Pulse_Syntax_Pure.tm_fvar
                                      (Pulse_Syntax_Base.as_fv
                                         (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                            "unit_non_informative")))
                               else
                                 if l = FStar_Reflection_Const.prop_qn
                                 then
                                   FStar_Pervasives_Native.Some
                                     (Pulse_Syntax_Pure.tm_fvar
                                        (Pulse_Syntax_Base.as_fv
                                           (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                              "prop_non_informative")))
                                 else
                                   if
                                     (l = FStar_Reflection_Const.squash_qn)
                                       &&
                                       (FStar_Pervasives_Native.uu___is_Some
                                          arg_opt)
                                   then
                                     FStar_Pervasives_Native.Some
                                       (Pulse_Syntax_Pure.tm_pureapp
                                          (Pulse_Syntax_Pure.tm_uinst
                                             (Pulse_Syntax_Base.as_fv
                                                (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                                   "squash_non_informative"))
                                             us) FStar_Pervasives_Native.None
                                          (FStar_Pervasives_Native.__proj__Some__item__v
                                             arg_opt))
                                   else
                                     if
                                       (l = Pulse_Reflection_Util.erased_lid)
                                         &&
                                         (FStar_Pervasives_Native.uu___is_Some
                                            arg_opt)
                                     then
                                       FStar_Pervasives_Native.Some
                                         (Pulse_Syntax_Pure.tm_pureapp
                                            (Pulse_Syntax_Pure.tm_uinst
                                               (Pulse_Syntax_Base.as_fv
                                                  (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                                     "erased_non_informative"))
                                               us)
                                            FStar_Pervasives_Native.None
                                            (FStar_Pervasives_Native.__proj__Some__item__v
                                               arg_opt))
                                     else FStar_Pervasives_Native.None
                           | uu___1 -> FStar_Pervasives_Native.None))
                     (fun uu___ ->
                        (fun eopt ->
                           match eopt with
                           | FStar_Pervasives_Native.None ->
                               Obj.magic (err ())
                           | FStar_Pervasives_Native.Some e ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (302))
                                             (Prims.of_int (8))
                                             (Prims.of_int (302))
                                             (Prims.of_int (126)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (300))
                                             (Prims.of_int (15))
                                             (Prims.of_int (303))
                                             (Prims.of_int (16)))))
                                    (Obj.magic
                                       (check_term_with_expected_type
                                          (Pulse_Typing_Env.push_context_no_range
                                             g "get_noninformative_witness")
                                          e
                                          (Pulse_Typing.non_informative_witness_t
                                             u t)))
                                    (fun uu___ ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            match uu___ with
                                            | Prims.Mkdtuple2 (x, y) ->
                                                Prims.Mkdtuple2 (x, ())))))
                          uu___))) uu___)
let (check_prop_validity :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        ((unit, unit) Pulse_Typing.prop_validity, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      fun uu___ ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (307)) (Prims.of_int (24))
                   (Prims.of_int (307)) (Prims.of_int (76)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (307)) (Prims.of_int (3))
                   (Prims.of_int (314)) (Prims.of_int (20)))))
          (Obj.magic
             (rtb_check_prop_validity g (Pulse_Typing.elab_env g)
                (Pulse_Elaborate_Pure.elab_term p)))
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (t_opt, issues) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (308)) (Prims.of_int (4))
                                  (Prims.of_int (308)) (Prims.of_int (23)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (309)) (Prims.of_int (4))
                                  (Prims.of_int (314)) (Prims.of_int (20)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.log_issues issues))
                         (fun uu___2 ->
                            (fun uu___2 ->
                               match t_opt with
                               | FStar_Pervasives_Native.None ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (312))
                                                    (Prims.of_int (13))
                                                    (Prims.of_int (313))
                                                    (Prims.of_int (62)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (311))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (313))
                                                    (Prims.of_int (62)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (313))
                                                          (Prims.of_int (22))
                                                          (Prims.of_int (313))
                                                          (Prims.of_int (61)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "prims.fst"
                                                          (Prims.of_int (590))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (590))
                                                          (Prims.of_int (31)))))
                                                 (Obj.magic
                                                    (Pulse_Syntax_Printer.term_to_string
                                                       p))
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 ->
                                                         Prims.strcat
                                                           "Failed to prove property: "
                                                           (Prims.strcat
                                                              uu___3 "\n")))))
                                           (fun uu___3 ->
                                              (fun uu___3 ->
                                                 Obj.magic
                                                   (Pulse_Typing_Env.fail g
                                                      (FStar_Pervasives_Native.Some
                                                         (p.Pulse_Syntax_Base.range1))
                                                      uu___3)) uu___3)))
                               | FStar_Pervasives_Native.Some tok ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> tok)))) uu___2)))
               uu___1)