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
        (((FStar_TypeChecker_Core.tot_or_ghost * FStar_Reflection_Types.typ)
           FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (24)) (Prims.of_int (2)) (Prims.of_int (27))
                   (Prims.of_int (31)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (27)) (Prims.of_int (32))
                   (Prims.of_int (29)) (Prims.of_int (5)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (27)) (Prims.of_int (10))
                              (Prims.of_int (27)) (Prims.of_int (30)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (25)) (Prims.of_int (4))
                              (Prims.of_int (27)) (Prims.of_int (30)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string e))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (25))
                                         (Prims.of_int (4))
                                         (Prims.of_int (27))
                                         (Prims.of_int (30)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (25))
                                         (Prims.of_int (4))
                                         (Prims.of_int (27))
                                         (Prims.of_int (30)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (26))
                                               (Prims.of_int (10))
                                               (Prims.of_int (26))
                                               (Prims.of_int (50)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Printf.fst"
                                               (Prims.of_int (121))
                                               (Prims.of_int (8))
                                               (Prims.of_int (123))
                                               (Prims.of_int (44)))))
                                      (Obj.magic
                                         (FStar_Tactics_V2_Builtins.range_to_string
                                            (Pulse_RuntimeUtils.range_of_term
                                               e)))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 ->
                                              fun x ->
                                                Prims.strcat
                                                  (Prims.strcat "("
                                                     (Prims.strcat uu___2
                                                        ") Calling core_check_term on "))
                                                  (Prims.strcat x "")))))
                                (fun uu___2 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> uu___2 uu___1)))) uu___1))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (28)) (Prims.of_int (12))
                              (Prims.of_int (28)) (Prims.of_int (42)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (28)) (Prims.of_int (6))
                              (Prims.of_int (28)) (Prims.of_int (9)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Builtins.core_compute_term_type f e))
                     (fun res ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> res))))
               uu___)
let (rtb_tc_term :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((FStar_Reflection_Types.term * (FStar_TypeChecker_Core.tot_or_ghost
           * FStar_Reflection_Types.typ)) FStar_Pervasives_Native.option *
           FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (33)) (Prims.of_int (10))
                   (Prims.of_int (33)) (Prims.of_int (51)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (34)) (Prims.of_int (2)) (Prims.of_int (39))
                   (Prims.of_int (5)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                Pulse_RuntimeUtils.deep_transform_to_unary_applications e))
          (fun uu___ ->
             (fun e1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (34)) (Prims.of_int (2))
                              (Prims.of_int (37)) (Prims.of_int (27)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (37)) (Prims.of_int (28))
                              (Prims.of_int (39)) (Prims.of_int (5)))))
                     (Obj.magic
                        (debug g
                           (fun uu___ ->
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (37))
                                         (Prims.of_int (6))
                                         (Prims.of_int (37))
                                         (Prims.of_int (26)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (35))
                                         (Prims.of_int (4))
                                         (Prims.of_int (37))
                                         (Prims.of_int (26)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Builtins.term_to_string
                                      e1))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (35))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (37))
                                                    (Prims.of_int (26)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (35))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (37))
                                                    (Prims.of_int (26)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (36))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (36))
                                                          (Prims.of_int (46)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Printf.fst"
                                                          (Prims.of_int (121))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (123))
                                                          (Prims.of_int (44)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_V2_Builtins.range_to_string
                                                       (Pulse_RuntimeUtils.range_of_term
                                                          e1)))
                                                 (fun uu___2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         fun x ->
                                                           Prims.strcat
                                                             (Prims.strcat
                                                                "("
                                                                (Prims.strcat
                                                                   uu___2
                                                                   ") Calling tc_term on "))
                                                             (Prims.strcat x
                                                                "")))))
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
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (38))
                                         (Prims.of_int (12))
                                         (Prims.of_int (38))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (38))
                                         (Prims.of_int (6))
                                         (Prims.of_int (38))
                                         (Prims.of_int (9)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Builtins.tc_term f e1))
                                (fun res ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> res)))) uu___))) uu___)
let (rtb_universe_of :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        ((FStar_Reflection_Types.universe FStar_Pervasives_Native.option *
           FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (42)) (Prims.of_int (2)) (Prims.of_int (45))
                   (Prims.of_int (27)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (45)) (Prims.of_int (28))
                   (Prims.of_int (47)) (Prims.of_int (5)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (45)) (Prims.of_int (6))
                              (Prims.of_int (45)) (Prims.of_int (26)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (43)) (Prims.of_int (4))
                              (Prims.of_int (45)) (Prims.of_int (26)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string e))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (43))
                                         (Prims.of_int (4))
                                         (Prims.of_int (45))
                                         (Prims.of_int (26)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (43))
                                         (Prims.of_int (4))
                                         (Prims.of_int (45))
                                         (Prims.of_int (26)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (44))
                                               (Prims.of_int (6))
                                               (Prims.of_int (44))
                                               (Prims.of_int (46)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Printf.fst"
                                               (Prims.of_int (121))
                                               (Prims.of_int (8))
                                               (Prims.of_int (123))
                                               (Prims.of_int (44)))))
                                      (Obj.magic
                                         (FStar_Tactics_V2_Builtins.range_to_string
                                            (Pulse_RuntimeUtils.range_of_term
                                               e)))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 ->
                                              fun x ->
                                                Prims.strcat
                                                  (Prims.strcat "("
                                                     (Prims.strcat uu___2
                                                        ") Calling universe_of on "))
                                                  (Prims.strcat x "")))))
                                (fun uu___2 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> uu___2 uu___1)))) uu___1))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (46)) (Prims.of_int (12))
                              (Prims.of_int (46)) (Prims.of_int (31)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (46)) (Prims.of_int (6))
                              (Prims.of_int (46)) (Prims.of_int (9)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.universe_of f e))
                     (fun res ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> res))))
               uu___)
let (rtb_check_subtyping :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (((unit, unit, unit) FStar_Tactics_Types.subtyping_token
           FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (50)) (Prims.of_int (2)) (Prims.of_int (55))
                   (Prims.of_int (30)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (55)) (Prims.of_int (31))
                   (Prims.of_int (57)) (Prims.of_int (5)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (55)) (Prims.of_int (8))
                              (Prims.of_int (55)) (Prims.of_int (29)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (51)) (Prims.of_int (4))
                              (Prims.of_int (55)) (Prims.of_int (29)))))
                     (Obj.magic (Pulse_Syntax_Printer.term_to_string t2))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (51))
                                         (Prims.of_int (4))
                                         (Prims.of_int (55))
                                         (Prims.of_int (29)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (51))
                                         (Prims.of_int (4))
                                         (Prims.of_int (55))
                                         (Prims.of_int (29)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (54))
                                               (Prims.of_int (8))
                                               (Prims.of_int (54))
                                               (Prims.of_int (29)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (51))
                                               (Prims.of_int (4))
                                               (Prims.of_int (55))
                                               (Prims.of_int (29)))))
                                      (Obj.magic
                                         (Pulse_Syntax_Printer.term_to_string
                                            t1))
                                      (fun uu___2 ->
                                         (fun uu___2 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (51))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (55))
                                                          (Prims.of_int (29)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (51))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (55))
                                                          (Prims.of_int (29)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Pure.fst"
                                                                (Prims.of_int (53))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (53))
                                                                (Prims.of_int (38)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Pure.fst"
                                                                (Prims.of_int (51))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (55))
                                                                (Prims.of_int (29)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_V2_Builtins.range_to_string
                                                             t2.Pulse_Syntax_Base.range1))
                                                       (fun uu___3 ->
                                                          (fun uu___3 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (29)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (29)))))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.range_to_string
                                                                    t1.Pulse_Syntax_Base.range1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "("
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    ", "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ") Calling check_subtyping on "))
                                                                    (Prims.strcat
                                                                    x1 " <: "))
                                                                    (Prims.strcat
                                                                    x2 "")))))
                                                                  (fun uu___4
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                            uu___3)))
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 ->
                                                         uu___3 uu___2))))
                                           uu___2)))
                                (fun uu___2 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> uu___2 uu___1)))) uu___1))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (56)) (Prims.of_int (12))
                              (Prims.of_int (56)) (Prims.of_int (74)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (56)) (Prims.of_int (6))
                              (Prims.of_int (56)) (Prims.of_int (9)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Builtins.check_subtyping
                           (Pulse_Typing.elab_env g)
                           (Pulse_Elaborate_Pure.elab_term t1)
                           (Pulse_Elaborate_Pure.elab_term t2)))
                     (fun res ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> res))))
               uu___)
let (rtb_instantiate_implicits :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((FStar_Reflection_Types.term * FStar_Reflection_Types.typ)
           FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (60)) (Prims.of_int (2)) (Prims.of_int (61))
                   (Prims.of_int (60)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (61)) (Prims.of_int (61))
                   (Prims.of_int (71)) (Prims.of_int (12)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (61)) (Prims.of_int (39))
                              (Prims.of_int (61)) (Prims.of_int (59)))))
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
                              (Prims.of_int (63)) (Prims.of_int (10))
                              (Prims.of_int (63)) (Prims.of_int (51)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (63)) (Prims.of_int (54))
                              (Prims.of_int (71)) (Prims.of_int (12)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           Pulse_RuntimeUtils.deep_transform_to_unary_applications
                             t))
                     (fun uu___1 ->
                        (fun t1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (64))
                                         (Prims.of_int (17))
                                         (Prims.of_int (64))
                                         (Prims.of_int (46)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (63))
                                         (Prims.of_int (54))
                                         (Prims.of_int (71))
                                         (Prims.of_int (12)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Builtins.instantiate_implicits
                                      f t1))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      match uu___1 with
                                      | (res, iss) ->
                                          (match res with
                                           | FStar_Pervasives_Native.None ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (67))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (67))
                                                             (Prims.of_int (66)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (68))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (68))
                                                             (Prims.of_int (12)))))
                                                    (Obj.magic
                                                       (debug g
                                                          (fun uu___2 ->
                                                             (fun uu___2 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    "Returned from instantiate_implicits: None")))
                                                               uu___2)))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            (res, iss))))
                                           | FStar_Pervasives_Native.Some
                                               (t2, uu___2) ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (70))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (70))
                                                             (Prims.of_int (100)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (71))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (71))
                                                             (Prims.of_int (12)))))
                                                    (Obj.magic
                                                       (debug g
                                                          (fun uu___3 ->
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (99)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_V2_Builtins.term_to_string
                                                                    t2))
                                                               (fun uu___4 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "Returned from instantiate_implicits: "
                                                                    (Prims.strcat
                                                                    uu___4 ""))))))
                                                    (fun uu___3 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___4 ->
                                                            (res, iss))))))
                                     uu___1))) uu___1))) uu___)
let (rtb_core_check_term_at_type :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        FStar_TypeChecker_Core.tot_or_ghost ->
          FStar_Reflection_Types.term ->
            (((unit, unit, unit) FStar_Tactics_Types.typing_token
               FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        fun eff ->
          fun t ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (74)) (Prims.of_int (2))
                       (Prims.of_int (78)) (Prims.of_int (37)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (78)) (Prims.of_int (38))
                       (Prims.of_int (80)) (Prims.of_int (5)))))
              (Obj.magic
                 (debug g
                    (fun uu___ ->
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (78)) (Prims.of_int (16))
                                  (Prims.of_int (78)) (Prims.of_int (36)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (75)) (Prims.of_int (4))
                                  (Prims.of_int (78)) (Prims.of_int (36)))))
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
                                             (Prims.of_int (75))
                                             (Prims.of_int (4))
                                             (Prims.of_int (78))
                                             (Prims.of_int (36)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (75))
                                             (Prims.of_int (4))
                                             (Prims.of_int (78))
                                             (Prims.of_int (36)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Pure.fst"
                                                   (Prims.of_int (77))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (77))
                                                   (Prims.of_int (36)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Pure.fst"
                                                   (Prims.of_int (75))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (78))
                                                   (Prims.of_int (36)))))
                                          (Obj.magic
                                             (FStar_Tactics_V2_Builtins.term_to_string
                                                e))
                                          (fun uu___2 ->
                                             (fun uu___2 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Pure.fst"
                                                              (Prims.of_int (75))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (78))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Pure.fst"
                                                              (Prims.of_int (75))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (78))
                                                              (Prims.of_int (36)))))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (56)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                           (Obj.magic
                                                              (FStar_Tactics_V2_Builtins.range_to_string
                                                                 (Pulse_RuntimeUtils.range_of_term
                                                                    e)))
                                                           (fun uu___3 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "("
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    ") Calling core_check_term on "))
                                                                    (Prims.strcat
                                                                    x " and "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
                                                     (fun uu___3 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             uu___3 uu___2))))
                                               uu___2)))
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
                                  (Prims.of_int (79)) (Prims.of_int (12))
                                  (Prims.of_int (79)) (Prims.of_int (41)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (79)) (Prims.of_int (6))
                                  (Prims.of_int (79)) (Prims.of_int (9)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.core_check_term f e t
                               eff))
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

let (rtb_check_prop_validity :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        ((unit FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun p ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (91)) (Prims.of_int (2)) (Prims.of_int (94))
                   (Prims.of_int (31)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (94)) (Prims.of_int (32))
                   (Prims.of_int (99)) (Prims.of_int (65)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (94)) (Prims.of_int (10))
                              (Prims.of_int (94)) (Prims.of_int (30)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (92)) (Prims.of_int (4))
                              (Prims.of_int (94)) (Prims.of_int (30)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string p))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (92))
                                         (Prims.of_int (4))
                                         (Prims.of_int (94))
                                         (Prims.of_int (30)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (92))
                                         (Prims.of_int (4))
                                         (Prims.of_int (94))
                                         (Prims.of_int (30)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (93))
                                               (Prims.of_int (10))
                                               (Prims.of_int (93))
                                               (Prims.of_int (50)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Printf.fst"
                                               (Prims.of_int (121))
                                               (Prims.of_int (8))
                                               (Prims.of_int (123))
                                               (Prims.of_int (44)))))
                                      (Obj.magic
                                         (FStar_Tactics_V2_Builtins.range_to_string
                                            (Pulse_RuntimeUtils.range_of_term
                                               p)))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 ->
                                              fun x ->
                                                Prims.strcat
                                                  (Prims.strcat "("
                                                     (Prims.strcat uu___2
                                                        ") Calling check_prop_validity on "))
                                                  (Prims.strcat x "")))))
                                (fun uu___2 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> uu___2 uu___1)))) uu___1))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (95)) (Prims.of_int (11))
                              (Prims.of_int (95)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (95)) (Prims.of_int (25))
                              (Prims.of_int (99)) (Prims.of_int (65)))))
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
                                         (Prims.of_int (96))
                                         (Prims.of_int (20))
                                         (Prims.of_int (96))
                                         (Prims.of_int (48)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (95))
                                         (Prims.of_int (25))
                                         (Prims.of_int (99))
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
                                                     ()), issues)))))) uu___1)))
               uu___)
let (exn_as_issue : Prims.exn -> FStar_Issue.issue) =
  fun e ->
    FStar_Issue.mk_issue_doc "Error"
      [FStar_Pprint.arbitrary_string (Pulse_RuntimeUtils.print_exn e)]
      FStar_Pervasives_Native.None FStar_Pervasives_Native.None []
let catch_all :
  'a .
    (unit ->
       (('a FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
         unit) FStar_Tactics_Effect.tac_repr)
      ->
      (('a FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
        unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (106)) (Prims.of_int (10)) (Prims.of_int (106))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (106)) (Prims.of_int (4)) (Prims.of_int (109))
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
               (Prims.of_int (113)) (Prims.of_int (17)) (Prims.of_int (113))
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
        (FStar_Pprint.document Prims.list, unit)
          FStar_Tactics_Effect.tac_repr)
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
                       (Prims.of_int (119)) (Prims.of_int (5))
                       (Prims.of_int (119)) (Prims.of_int (36)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (119)) (Prims.of_int (4))
                       (Prims.of_int (119)) (Prims.of_int (37)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (119)) (Prims.of_int (32))
                             (Prims.of_int (119)) (Prims.of_int (36)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (119)) (Prims.of_int (5))
                             (Prims.of_int (119)) (Prims.of_int (36)))))
                    (Obj.magic (Pulse_PP.pp Pulse_PP.uu___44 t))
                    (fun uu___1 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___2 ->
                            FStar_Pprint.op_Hat_Hat
                              (Pulse_PP.text "Ill-typed term: ") uu___1))))
              (fun uu___1 ->
                 FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> [uu___1]))
        | (FStar_Pervasives_Native.Some ty, FStar_Pervasives_Native.None) ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (121)) (Prims.of_int (5))
                       (Prims.of_int (122)) (Prims.of_int (37)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (121)) (Prims.of_int (4))
                       (Prims.of_int (122)) (Prims.of_int (38)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (121)) (Prims.of_int (5))
                             (Prims.of_int (121)) (Prims.of_int (51)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (121)) (Prims.of_int (5))
                             (Prims.of_int (122)) (Prims.of_int (37)))))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (121)) (Prims.of_int (11))
                                   (Prims.of_int (121)) (Prims.of_int (51)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (121)) (Prims.of_int (5))
                                   (Prims.of_int (121)) (Prims.of_int (51)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (121))
                                         (Prims.of_int (45))
                                         (Prims.of_int (121))
                                         (Prims.of_int (50)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (121))
                                         (Prims.of_int (11))
                                         (Prims.of_int (121))
                                         (Prims.of_int (51)))))
                                (Obj.magic (Pulse_PP.pp Pulse_PP.uu___44 ty))
                                (fun uu___ ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        FStar_Pprint.op_Hat_Slash_Hat
                                          (Pulse_PP.text
                                             "Expected term of type") uu___))))
                          (fun uu___ ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> FStar_Pprint.group uu___))))
                    (fun uu___ ->
                       (fun uu___ ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Pure.fst"
                                        (Prims.of_int (122))
                                        (Prims.of_int (5))
                                        (Prims.of_int (122))
                                        (Prims.of_int (37)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Pure.fst"
                                        (Prims.of_int (121))
                                        (Prims.of_int (5))
                                        (Prims.of_int (122))
                                        (Prims.of_int (37)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Pure.fst"
                                              (Prims.of_int (122))
                                              (Prims.of_int (11))
                                              (Prims.of_int (122))
                                              (Prims.of_int (37)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Pure.fst"
                                              (Prims.of_int (122))
                                              (Prims.of_int (5))
                                              (Prims.of_int (122))
                                              (Prims.of_int (37)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (122))
                                                    (Prims.of_int (32))
                                                    (Prims.of_int (122))
                                                    (Prims.of_int (36)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (122))
                                                    (Prims.of_int (11))
                                                    (Prims.of_int (122))
                                                    (Prims.of_int (37)))))
                                           (Obj.magic
                                              (Pulse_PP.pp Pulse_PP.uu___44 t))
                                           (fun uu___1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pprint.op_Hat_Slash_Hat
                                                     (Pulse_PP.text
                                                        "got term") uu___1))))
                                     (fun uu___1 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 ->
                                             FStar_Pprint.group uu___1))))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       FStar_Pprint.op_Hat_Slash_Hat uu___
                                         uu___1)))) uu___)))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> [uu___]))
        | (FStar_Pervasives_Native.Some ty, FStar_Pervasives_Native.Some ty')
            ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (124)) (Prims.of_int (5))
                       (Prims.of_int (126)) (Prims.of_int (38)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (124)) (Prims.of_int (4))
                       (Prims.of_int (126)) (Prims.of_int (39)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (124)) (Prims.of_int (5))
                             (Prims.of_int (124)) (Prims.of_int (51)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (124)) (Prims.of_int (5))
                             (Prims.of_int (126)) (Prims.of_int (38)))))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (124)) (Prims.of_int (11))
                                   (Prims.of_int (124)) (Prims.of_int (51)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (124)) (Prims.of_int (5))
                                   (Prims.of_int (124)) (Prims.of_int (51)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (124))
                                         (Prims.of_int (45))
                                         (Prims.of_int (124))
                                         (Prims.of_int (50)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (124))
                                         (Prims.of_int (11))
                                         (Prims.of_int (124))
                                         (Prims.of_int (51)))))
                                (Obj.magic (Pulse_PP.pp Pulse_PP.uu___44 ty))
                                (fun uu___ ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        FStar_Pprint.op_Hat_Slash_Hat
                                          (Pulse_PP.text
                                             "Expected term of type") uu___))))
                          (fun uu___ ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> FStar_Pprint.group uu___))))
                    (fun uu___ ->
                       (fun uu___ ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Pure.fst"
                                        (Prims.of_int (125))
                                        (Prims.of_int (5))
                                        (Prims.of_int (126))
                                        (Prims.of_int (38)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Pure.fst"
                                        (Prims.of_int (124))
                                        (Prims.of_int (5))
                                        (Prims.of_int (126))
                                        (Prims.of_int (38)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Pure.fst"
                                              (Prims.of_int (125))
                                              (Prims.of_int (5))
                                              (Prims.of_int (125))
                                              (Prims.of_int (37)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Pure.fst"
                                              (Prims.of_int (125))
                                              (Prims.of_int (5))
                                              (Prims.of_int (126))
                                              (Prims.of_int (38)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (125))
                                                    (Prims.of_int (11))
                                                    (Prims.of_int (125))
                                                    (Prims.of_int (37)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (125))
                                                    (Prims.of_int (5))
                                                    (Prims.of_int (125))
                                                    (Prims.of_int (37)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (125))
                                                          (Prims.of_int (32))
                                                          (Prims.of_int (125))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (125))
                                                          (Prims.of_int (11))
                                                          (Prims.of_int (125))
                                                          (Prims.of_int (37)))))
                                                 (Obj.magic
                                                    (Pulse_PP.pp
                                                       Pulse_PP.uu___44 t))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         FStar_Pprint.op_Hat_Slash_Hat
                                                           (Pulse_PP.text
                                                              "got term")
                                                           uu___1))))
                                           (fun uu___1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pprint.group uu___1))))
                                     (fun uu___1 ->
                                        (fun uu___1 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Pure.fst"
                                                         (Prims.of_int (126))
                                                         (Prims.of_int (5))
                                                         (Prims.of_int (126))
                                                         (Prims.of_int (38)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Pure.fst"
                                                         (Prims.of_int (125))
                                                         (Prims.of_int (5))
                                                         (Prims.of_int (126))
                                                         (Prims.of_int (38)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (126))
                                                               (Prims.of_int (11))
                                                               (Prims.of_int (126))
                                                               (Prims.of_int (38)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (126))
                                                               (Prims.of_int (5))
                                                               (Prims.of_int (126))
                                                               (Prims.of_int (38)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (37)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (38)))))
                                                            (Obj.magic
                                                               (Pulse_PP.pp
                                                                  Pulse_PP.uu___44
                                                                  ty'))
                                                            (fun uu___2 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___3
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "of type")
                                                                    uu___2))))
                                                      (fun uu___2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 ->
                                                              FStar_Pprint.group
                                                                uu___2))))
                                                (fun uu___2 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        FStar_Pprint.op_Hat_Slash_Hat
                                                          uu___1 uu___2))))
                                          uu___1)))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       FStar_Pprint.op_Hat_Slash_Hat uu___
                                         uu___1)))) uu___)))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> [uu___]))
let maybe_fail_doc :
  'uuuuu .
    FStar_Issue.issue Prims.list ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.range ->
          FStar_Pprint.document Prims.list ->
            ('uuuuu, unit) FStar_Tactics_Effect.tac_repr
  =
  fun issues ->
    fun g ->
      fun rng ->
        fun doc ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (131)) (Prims.of_int (6))
                     (Prims.of_int (135)) (Prims.of_int (14)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (137)) (Prims.of_int (2))
                     (Prims.of_int (140)) (Prims.of_int (32)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  FStar_List_Tot_Base.existsb
                    (fun i ->
                       ((FStar_Issue.level_of_issue i) = "Error") &&
                         (FStar_Pervasives_Native.uu___is_Some
                            (FStar_Issue.range_of_issue i))) issues))
            (fun uu___ ->
               (fun has_localized_error ->
                  if has_localized_error
                  then
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (138)) (Prims.of_int (41))
                                  (Prims.of_int (138)) (Prims.of_int (83)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (139)) (Prims.of_int (7))
                                  (Prims.of_int (139)) (Prims.of_int (21)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               FStar_Pprint.pretty_string
                                 Pulse_RuntimeUtils.float_one
                                 (Prims.of_int (80))
                                 (FStar_Pprint.concat doc)))
                         (fun message ->
                            FStar_Tactics_V2_Derived.fail message))
                  else
                    Obj.magic
                      (Pulse_Typing_Env.fail_doc g
                         (FStar_Pervasives_Native.Some rng) doc)) uu___)
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
                 (Prims.of_int (143)) (Prims.of_int (10))
                 (Prims.of_int (143)) (Prims.of_int (20)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (143)) (Prims.of_int (23))
                 (Prims.of_int (165)) (Prims.of_int (49)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun f ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (144)) (Prims.of_int (11))
                            (Prims.of_int (144)) (Prims.of_int (23)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (144)) (Prims.of_int (26))
                            (Prims.of_int (165)) (Prims.of_int (49)))))
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
                                       (Prims.of_int (145))
                                       (Prims.of_int (10))
                                       (Prims.of_int (145))
                                       (Prims.of_int (75)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (145))
                                       (Prims.of_int (78))
                                       (Prims.of_int (165))
                                       (Prims.of_int (49)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (145))
                                             (Prims.of_int (29))
                                             (Prims.of_int (145))
                                             (Prims.of_int (75)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (145))
                                             (Prims.of_int (10))
                                             (Prims.of_int (145))
                                             (Prims.of_int (75)))))
                                    (Obj.magic
                                       (Pulse_Typing_Env.get_range g
                                          (FStar_Pervasives_Native.Some
                                             (t0.Pulse_Syntax_Base.range1))))
                                    (fun uu___ ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            Pulse_RuntimeUtils.env_set_range
                                              f uu___))))
                              (fun uu___ ->
                                 (fun f1 ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (146))
                                                  (Prims.of_int (21))
                                                  (Prims.of_int (146))
                                                  (Prims.of_int (74)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (145))
                                                  (Prims.of_int (78))
                                                  (Prims.of_int (165))
                                                  (Prims.of_int (49)))))
                                         (Obj.magic
                                            (catch_all
                                               (fun uu___ ->
                                                  rtb_instantiate_implicits g
                                                    f1 rt)))
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
                                                                 (Prims.of_int (147))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (147))
                                                                 (Prims.of_int (21)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Pure.fst"
                                                                 (Prims.of_int (148))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (165))
                                                                 (Prims.of_int (49)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Builtins.log_issues
                                                              issues))
                                                        (fun uu___1 ->
                                                           (fun uu___1 ->
                                                              match topt with
                                                              | FStar_Pervasives_Native.None
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.uu___44
                                                                    t0))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Could not infer implicit arguments in")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    [uu___2]))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    t0.Pulse_Syntax_Base.range1
                                                                    uu___2))
                                                                    uu___2))
                                                              | FStar_Pervasives_Native.Some
                                                                  (t, ty) ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Readback.readback_ty
                                                                    t))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    topt1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (165))
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
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (163))
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
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (165))
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
                                                             uu___1))) uu___)))
                                   uu___))) uu___))) uu___)
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
                 (Prims.of_int (169)) (Prims.of_int (12))
                 (Prims.of_int (169)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (169)) (Prims.of_int (25))
                 (Prims.of_int (184)) (Prims.of_int (23)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun f ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (170)) (Prims.of_int (13))
                            (Prims.of_int (170)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (170)) (Prims.of_int (27))
                            (Prims.of_int (184)) (Prims.of_int (23)))))
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
                                       (Prims.of_int (171))
                                       (Prims.of_int (25))
                                       (Prims.of_int (171))
                                       (Prims.of_int (68)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (170))
                                       (Prims.of_int (27))
                                       (Prims.of_int (184))
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
                                                      (Prims.of_int (172))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (172))
                                                      (Prims.of_int (23)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (173))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (184))
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
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (68)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (68)))))
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
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    t.Pulse_Syntax_Base.range1
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
        (((FStar_Reflection_Types.term, FStar_TypeChecker_Core.tot_or_ghost,
           FStar_Reflection_Types.term,
           (unit, unit, unit) FStar_Reflection_Typing.typing)
           FStar_Pervasives.dtuple4 FStar_Pervasives_Native.option *
           FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (189)) (Prims.of_int (6))
                   (Prims.of_int (194)) (Prims.of_int (14)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (188)) (Prims.of_int (8))
                   (Prims.of_int (188)) (Prims.of_int (11)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (189)) (Prims.of_int (12))
                         (Prims.of_int (189)) (Prims.of_int (50)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (189)) (Prims.of_int (6))
                         (Prims.of_int (194)) (Prims.of_int (14)))))
                (Obj.magic (catch_all (fun uu___ -> rtb_tc_term g f e)))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        match uu___ with
                        | (FStar_Pervasives_Native.None, issues) ->
                            (FStar_Pervasives_Native.None, issues)
                        | (FStar_Pervasives_Native.Some (e1, (eff, t)),
                           issues) ->
                            ((FStar_Pervasives_Native.Some
                                (FStar_Pervasives.Mkdtuple4
                                   (e1, eff, t,
                                     (FStar_Reflection_Typing.T_Token
                                        (f, e1, (eff, t), ()))))), issues)))))
          (fun res -> FStar_Tactics_Effect.lift_div_tac (fun uu___ -> res))
let (check_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, FStar_TypeChecker_Core.tot_or_ghost,
         Pulse_Syntax_Base.term, unit) FStar_Pervasives.dtuple4,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (203)) (Prims.of_int (13))
                 (Prims.of_int (203)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (203)) (Prims.of_int (26))
                 (Prims.of_int (219)) (Prims.of_int (50)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun fg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (204)) (Prims.of_int (13))
                            (Prims.of_int (204)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (205)) (Prims.of_int (4))
                            (Prims.of_int (219)) (Prims.of_int (50)))))
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
                                       (Prims.of_int (205))
                                       (Prims.of_int (4))
                                       (Prims.of_int (208))
                                       (Prims.of_int (44)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (208))
                                       (Prims.of_int (45))
                                       (Prims.of_int (219))
                                       (Prims.of_int (50)))))
                              (Obj.magic
                                 (debug g
                                    (fun uu___ ->
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (208))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (208))
                                                  (Prims.of_int (43)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (206))
                                                  (Prims.of_int (12))
                                                  (Prims.of_int (208))
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
                                                             (Prims.of_int (206))
                                                             (Prims.of_int (12))
                                                             (Prims.of_int (208))
                                                             (Prims.of_int (43)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (206))
                                                             (Prims.of_int (12))
                                                             (Prims.of_int (208))
                                                             (Prims.of_int (43)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (207))
                                                                   (Prims.of_int (22))
                                                                   (Prims.of_int (207))
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
                                                  (Prims.of_int (209))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (209))
                                                  (Prims.of_int (46)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (208))
                                                  (Prims.of_int (45))
                                                  (Prims.of_int (219))
                                                  (Prims.of_int (50)))))
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
                                                                 (Prims.of_int (210))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (210))
                                                                 (Prims.of_int (23)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Pure.fst"
                                                                 (Prims.of_int (211))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (219))
                                                                 (Prims.of_int (50)))))
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
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (50)))))
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
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    t.Pulse_Syntax_Base.range1
                                                                    uu___3))
                                                                    uu___3)))
                                                              | FStar_Pervasives_Native.Some
                                                                  (FStar_Pervasives.Mkdtuple4
                                                                  (rt1, eff,
                                                                   ty', tok))
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
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (217))
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
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (218))
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
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (t1, eff,
                                                                    ty, ()))))))
                                                             uu___2))) uu___1)))
                                   uu___))) uu___))) uu___)
let (check_term_and_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, FStar_TypeChecker_Core.tot_or_ghost,
         Pulse_Syntax_Base.term,
         (Pulse_Syntax_Base.universe, unit) Prims.dtuple2, unit)
         FStar_Pervasives.dtuple5,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (228)) (Prims.of_int (13))
                 (Prims.of_int (228)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (228)) (Prims.of_int (26))
                 (Prims.of_int (243)) (Prims.of_int (45)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun fg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (229)) (Prims.of_int (13))
                            (Prims.of_int (229)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (229)) (Prims.of_int (27))
                            (Prims.of_int (243)) (Prims.of_int (45)))))
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
                                       (Prims.of_int (230))
                                       (Prims.of_int (22))
                                       (Prims.of_int (230))
                                       (Prims.of_int (46)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (229))
                                       (Prims.of_int (27))
                                       (Prims.of_int (243))
                                       (Prims.of_int (45)))))
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
                                                      (Prims.of_int (231))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (231))
                                                      (Prims.of_int (23)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (232))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (243))
                                                      (Prims.of_int (45)))))
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
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (46)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (46)))))
                                                            (Obj.magic
                                                               (ill_typed_term
                                                                  t
                                                                  FStar_Pervasives_Native.None
                                                                  FStar_Pervasives_Native.None))
                                                            (fun uu___2 ->
                                                               (fun uu___2 ->
                                                                  Obj.magic
                                                                    (
                                                                    maybe_fail_doc
                                                                    issues g
                                                                    t.Pulse_Syntax_Base.range1
                                                                    uu___2))
                                                                 uu___2))
                                                   | FStar_Pervasives_Native.Some
                                                       (FStar_Pervasives.Mkdtuple4
                                                       (rt1, eff, ty', tok))
                                                       ->
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
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (62)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (239))
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
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (63)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (240))
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
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (46)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (45)))))
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
                                                                    (t1, eff,
                                                                    ty,
                                                                    (Prims.Mkdtuple2
                                                                    (u, ())),
                                                                    ()))))))
                                                  uu___1))) uu___))) uu___)))
             uu___)
let (check_term_with_expected_type_and_effect :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      FStar_TypeChecker_Core.tot_or_ghost ->
        Pulse_Syntax_Base.term ->
          ((Pulse_Syntax_Base.term, unit) Prims.dtuple2, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun eff ->
        fun t ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (248)) (Prims.of_int (13))
                     (Prims.of_int (248)) (Prims.of_int (43)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (246)) (Prims.of_int (39))
                     (Prims.of_int (265)) (Prims.of_int (78)))))
            (Obj.magic (instantiate_term_implicits g e))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | (e1, uu___1) ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Pure.fst"
                                    (Prims.of_int (250)) (Prims.of_int (11))
                                    (Prims.of_int (250)) (Prims.of_int (21)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Pure.fst"
                                    (Prims.of_int (250)) (Prims.of_int (24))
                                    (Prims.of_int (265)) (Prims.of_int (78)))))
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
                                               (Prims.of_int (251))
                                               (Prims.of_int (11))
                                               (Prims.of_int (251))
                                               (Prims.of_int (22)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (251))
                                               (Prims.of_int (25))
                                               (Prims.of_int (265))
                                               (Prims.of_int (78)))))
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
                                                          (Prims.of_int (252))
                                                          (Prims.of_int (11))
                                                          (Prims.of_int (252))
                                                          (Prims.of_int (22)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (252))
                                                          (Prims.of_int (25))
                                                          (Prims.of_int (265))
                                                          (Prims.of_int (78)))))
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
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (20)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (78)))))
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
                                                                    re eff rt)))
                                                            (fun uu___2 ->
                                                               (fun uu___2 ->
                                                                  match uu___2
                                                                  with
                                                                  | (topt,
                                                                    issues)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (78)))))
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
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (48)))))
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
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    e1.Pulse_Syntax_Base.range1
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
                                                                    (e1, ())))))
                                                                    uu___3)))
                                                                 uu___2)))
                                                      uu___2))) uu___2)))
                                uu___2))) uu___)
let (check_term_with_expected_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        ((Pulse_Syntax_Base.term, FStar_TypeChecker_Core.tot_or_ghost, 
           unit) FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun t ->
        FStar_Tactics_V2_Derived.try_with
          (fun uu___ ->
             match () with
             | () ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (273)) (Prims.of_int (22))
                            (Prims.of_int (273)) (Prims.of_int (78)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (272)) (Prims.of_int (5))
                            (Prims.of_int (274)) (Prims.of_int (78)))))
                   (Obj.magic
                      (check_term_with_expected_type_and_effect g e
                         FStar_TypeChecker_Core.E_Total t))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           match uu___1 with
                           | Prims.Mkdtuple2 (e1, et) ->
                               FStar_Pervasives.Mkdtuple3
                                 (e1, FStar_TypeChecker_Core.E_Total, ()))))
          (fun uu___ ->
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (276)) (Prims.of_int (22))
                        (Prims.of_int (276)) (Prims.of_int (78)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (275)) (Prims.of_int (13))
                        (Prims.of_int (277)) (Prims.of_int (26)))))
               (Obj.magic
                  (check_term_with_expected_type_and_effect g e
                     FStar_TypeChecker_Core.E_Ghost t))
               (fun uu___1 ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___2 ->
                       match uu___1 with
                       | Prims.Mkdtuple2 (e1, et) ->
                           FStar_Pervasives.Mkdtuple3
                             (e1, FStar_TypeChecker_Core.E_Ghost, ()))))
let (tc_with_core :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((FStar_TypeChecker_Core.tot_or_ghost, FStar_Reflection_Types.term,
           (unit, unit, unit) FStar_Reflection_Typing.typing)
           FStar_Pervasives.dtuple3 FStar_Pervasives_Native.option *
           FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (281)) (Prims.of_int (23))
                   (Prims.of_int (281)) (Prims.of_int (117)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (281)) (Prims.of_int (3))
                   (Prims.of_int (285)) (Prims.of_int (76)))))
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
                       | FStar_Pervasives_Native.Some (eff, t) ->
                           ((FStar_Pervasives_Native.Some
                               (FStar_Pervasives.Mkdtuple3
                                  (eff, t,
                                    (FStar_Reflection_Typing.T_Token
                                       (f, e, (eff, t), ()))))), issues))))
let (core_check_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((FStar_TypeChecker_Core.tot_or_ghost, Pulse_Syntax_Base.term, 
         unit) FStar_Pervasives.dtuple3,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (291)) (Prims.of_int (13))
                 (Prims.of_int (291)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (291)) (Prims.of_int (26))
                 (Prims.of_int (305)) (Prims.of_int (30)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun fg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (292)) (Prims.of_int (13))
                            (Prims.of_int (292)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (292)) (Prims.of_int (27))
                            (Prims.of_int (305)) (Prims.of_int (30)))))
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
                                       (Prims.of_int (293))
                                       (Prims.of_int (22))
                                       (Prims.of_int (293))
                                       (Prims.of_int (94)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (292))
                                       (Prims.of_int (27))
                                       (Prims.of_int (305))
                                       (Prims.of_int (30)))))
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
                                                      (Prims.of_int (294))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (294))
                                                      (Prims.of_int (23)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (295))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (305))
                                                      (Prims.of_int (30)))))
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
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (46)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (46)))))
                                                               (Obj.magic
                                                                  (ill_typed_term
                                                                    t
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Pervasives_Native.None))
                                                               (fun uu___2 ->
                                                                  (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    t.Pulse_Syntax_Base.range1
                                                                    uu___2))
                                                                    uu___2)))
                                                   | FStar_Pervasives_Native.Some
                                                       (FStar_Pervasives.Mkdtuple3
                                                       (eff, ty', tok)) ->
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
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (303))
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
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eff, ty,
                                                                    ()))))))
                                                  uu___1))) uu___))) uu___)))
             uu___)
let (core_check_term_with_expected_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      FStar_TypeChecker_Core.tot_or_ghost ->
        Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun eff ->
        fun t ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (308)) (Prims.of_int (11))
                     (Prims.of_int (308)) (Prims.of_int (21)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (308)) (Prims.of_int (24))
                     (Prims.of_int (322)) (Prims.of_int (69)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_Typing.elab_env g))
            (fun uu___ ->
               (fun fg ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (309)) (Prims.of_int (11))
                                (Prims.of_int (309)) (Prims.of_int (22)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (309)) (Prims.of_int (25))
                                (Prims.of_int (322)) (Prims.of_int (69)))))
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
                                           (Prims.of_int (310))
                                           (Prims.of_int (11))
                                           (Prims.of_int (310))
                                           (Prims.of_int (22)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (310))
                                           (Prims.of_int (25))
                                           (Prims.of_int (322))
                                           (Prims.of_int (69)))))
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
                                                      (Prims.of_int (312))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (315))
                                                      (Prims.of_int (20)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (310))
                                                      (Prims.of_int (25))
                                                      (Prims.of_int (322))
                                                      (Prims.of_int (69)))))
                                             (Obj.magic
                                                (catch_all
                                                   (fun uu___ ->
                                                      rtb_core_check_term_at_type
                                                        (Pulse_Typing_Env.push_context
                                                           g
                                                           "core_check_term_with_expected_type"
                                                           (FStar_Reflection_V2_Builtins.range_of_term
                                                              rt)) fg re eff
                                                        rt)))
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
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (21)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (69)))))
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
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (48)))))
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
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    e.Pulse_Syntax_Base.range1
                                                                    uu___2))
                                                                    uu___2)))
                                                                  | FStar_Pervasives_Native.Some
                                                                    tok ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))))
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
      check_term_with_expected_type_and_effect
        (Pulse_Typing_Env.push_context_no_range g "check_vprop") t
        FStar_TypeChecker_Core.E_Total Pulse_Syntax_Base.tm_vprop
let (check_vprop_with_core :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      core_check_term_with_expected_type
        (Pulse_Typing_Env.push_context_no_range g "check_vprop_with_core") t
        FStar_TypeChecker_Core.E_Total Pulse_Syntax_Base.tm_vprop
let (pulse_lib_gref : Prims.string Prims.list) =
  ["Pulse"; "Lib"; "GhostReference"]
let (mk_pulse_lib_gref_lid : Prims.string -> Prims.string Prims.list) =
  fun s -> FStar_List_Tot_Base.op_At pulse_lib_gref [s]
let (gref_lid : Prims.string Prims.list) = mk_pulse_lib_gref_lid "ref"
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
                   (Prims.of_int (345)) (Prims.of_int (6))
                   (Prims.of_int (349)) (Prims.of_int (7)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (350)) (Prims.of_int (6))
                   (Prims.of_int (384)) (Prims.of_int (39)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun uu___1 ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (346)) (Prims.of_int (32))
                             (Prims.of_int (349)) (Prims.of_int (7)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (346)) (Prims.of_int (6))
                             (Prims.of_int (349)) (Prims.of_int (7)))))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (347)) (Prims.of_int (8))
                                   (Prims.of_int (348)) (Prims.of_int (18)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (346)) (Prims.of_int (32))
                                   (Prims.of_int (349)) (Prims.of_int (7)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (348))
                                         (Prims.of_int (14))
                                         (Prims.of_int (348))
                                         (Prims.of_int (18)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (347))
                                         (Prims.of_int (8))
                                         (Prims.of_int (348))
                                         (Prims.of_int (18)))))
                                (Obj.magic (Pulse_PP.pp Pulse_PP.uu___44 t))
                                (fun uu___2 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 ->
                                        FStar_Pprint.op_Hat_Slash_Hat
                                          (Pulse_PP.text
                                             "Expected a term with a non-informative (e.g., erased) type; got")
                                          uu___2))))
                          (fun uu___2 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 -> [uu___2]))))
                    (fun uu___2 ->
                       (fun uu___2 ->
                          Obj.magic
                            (Pulse_Typing_Env.fail_doc g
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
                              (Prims.of_int (351)) (Prims.of_int (14))
                              (Prims.of_int (375)) (Prims.of_int (17)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (377)) (Prims.of_int (4))
                              (Prims.of_int (384)) (Prims.of_int (39)))))
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
                                         (Pulse_Reflection_Util.mk_pulse_lib_core_lid
                                            "unit_non_informative")))
                               else
                                 if l = FStar_Reflection_Const.prop_qn
                                 then
                                   FStar_Pervasives_Native.Some
                                     (Pulse_Syntax_Pure.tm_fvar
                                        (Pulse_Syntax_Base.as_fv
                                           (Pulse_Reflection_Util.mk_pulse_lib_core_lid
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
                                                (Pulse_Reflection_Util.mk_pulse_lib_core_lid
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
                                                  (Pulse_Reflection_Util.mk_pulse_lib_core_lid
                                                     "erased_non_informative"))
                                               us)
                                            FStar_Pervasives_Native.None
                                            (FStar_Pervasives_Native.__proj__Some__item__v
                                               arg_opt))
                                     else
                                       if
                                         (l = gref_lid) &&
                                           (FStar_Pervasives_Native.uu___is_Some
                                              arg_opt)
                                       then
                                         FStar_Pervasives_Native.Some
                                           (Pulse_Syntax_Pure.tm_pureapp
                                              (Pulse_Syntax_Pure.tm_uinst
                                                 (Pulse_Syntax_Base.as_fv
                                                    (mk_pulse_lib_gref_lid
                                                       "gref_non_informative"))
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
                                 (check_term_with_expected_type_and_effect
                                    (Pulse_Typing_Env.push_context_no_range g
                                       "get_noninformative_witness") e
                                    FStar_TypeChecker_Core.E_Total
                                    (Pulse_Typing.non_informative_witness_t u
                                       t))) uu___))) uu___)
let (check_prop_validity :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      fun uu___ ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (388)) (Prims.of_int (24))
                   (Prims.of_int (388)) (Prims.of_int (76)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (388)) (Prims.of_int (3))
                   (Prims.of_int (395)) (Prims.of_int (21)))))
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
                                  (Prims.of_int (389)) (Prims.of_int (4))
                                  (Prims.of_int (389)) (Prims.of_int (23)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (390)) (Prims.of_int (4))
                                  (Prims.of_int (395)) (Prims.of_int (21)))))
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
                                                    (Prims.of_int (394))
                                                    (Prims.of_int (21))
                                                    (Prims.of_int (394))
                                                    (Prims.of_int (64)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (393))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (394))
                                                    (Prims.of_int (64)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (394))
                                                          (Prims.of_int (22))
                                                          (Prims.of_int (394))
                                                          (Prims.of_int (63)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (394))
                                                          (Prims.of_int (21))
                                                          (Prims.of_int (394))
                                                          (Prims.of_int (64)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Pure.fst"
                                                                (Prims.of_int (394))
                                                                (Prims.of_int (59))
                                                                (Prims.of_int (394))
                                                                (Prims.of_int (63)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Pure.fst"
                                                                (Prims.of_int (394))
                                                                (Prims.of_int (22))
                                                                (Prims.of_int (394))
                                                                (Prims.of_int (63)))))
                                                       (Obj.magic
                                                          (Pulse_PP.pp
                                                             Pulse_PP.uu___44
                                                             p))
                                                       (fun uu___3 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               FStar_Pprint.op_Hat_Slash_Hat
                                                                 (Pulse_PP.text
                                                                    "Failed to prove property:")
                                                                 uu___3))))
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 -> [uu___3]))))
                                           (fun uu___3 ->
                                              (fun uu___3 ->
                                                 Obj.magic
                                                   (maybe_fail_doc issues g
                                                      p.Pulse_Syntax_Base.range1
                                                      uu___3)) uu___3)))
                               | FStar_Pervasives_Native.Some tok ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> ())))) uu___2)))
               uu___1)
let fail_expected_tot_found_ghost :
  'uuuuu .
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term -> ('uuuuu, unit) FStar_Tactics_Effect.tac_repr
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (399)) (Prims.of_int (4)) (Prims.of_int (399))
                 (Prims.of_int (86)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (398)) (Prims.of_int (2)) (Prims.of_int (399))
                 (Prims.of_int (86)))))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (399)) (Prims.of_int (65))
                       (Prims.of_int (399)) (Prims.of_int (85)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                       (Prims.of_int (19)) (Prims.of_int (590))
                       (Prims.of_int (31)))))
              (Obj.magic (Pulse_Syntax_Printer.term_to_string t))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      Prims.strcat "Expected a total term, found ghost term "
                        (Prims.strcat uu___ "")))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (Pulse_Typing_Env.fail g
                   (FStar_Pervasives_Native.Some (t.Pulse_Syntax_Base.range1))
                   uu___)) uu___)
let (check_tot_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, Pulse_Syntax_Base.typ, unit)
         FStar_Pervasives.dtuple3,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (402)) (Prims.of_int (35))
                 (Prims.of_int (402)) (Prims.of_int (49)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (401)) (Prims.of_int (24))
                 (Prims.of_int (404)) (Prims.of_int (40)))))
        (Obj.magic (check_term g t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives.Mkdtuple4 (t1, eff, ty, t_typing) ->
                  if eff = FStar_TypeChecker_Core.E_Total
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Pervasives.Mkdtuple3 (t1, ty, ()))))
                  else
                    Obj.magic (Obj.repr (fail_expected_tot_found_ghost g t1)))
             uu___)
let (check_tot_term_and_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, Pulse_Syntax_Base.universe,
         Pulse_Syntax_Base.typ, unit, unit) FStar_Pervasives.dtuple5,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (407)) (Prims.of_int (55))
                 (Prims.of_int (407)) (Prims.of_int (78)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (406)) (Prims.of_int (33))
                 (Prims.of_int (409)) (Prims.of_int (40)))))
        (Obj.magic (check_term_and_type g t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives.Mkdtuple5
                  (t1, eff, ty, Prims.Mkdtuple2 (u, ty_typing), t_typing) ->
                  if eff = FStar_TypeChecker_Core.E_Total
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Pervasives.Mkdtuple5 (t1, u, ty, (), ()))))
                  else
                    Obj.magic (Obj.repr (fail_expected_tot_found_ghost g t1)))
             uu___)
let (check_tot_term_with_expected_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        ((Pulse_Syntax_Base.term, unit) Prims.dtuple2, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun t ->
        check_term_with_expected_type_and_effect g e
          FStar_TypeChecker_Core.E_Total t
let (core_check_tot_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.typ, unit) Prims.dtuple2, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (415)) (Prims.of_int (25))
                 (Prims.of_int (415)) (Prims.of_int (44)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (414)) (Prims.of_int (29))
                 (Prims.of_int (417)) (Prims.of_int (40)))))
        (Obj.magic (core_check_term g t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives.Mkdtuple3 (eff, ty, d) ->
                  if eff = FStar_TypeChecker_Core.E_Total
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> Prims.Mkdtuple2 (ty, ()))))
                  else
                    Obj.magic (Obj.repr (fail_expected_tot_found_ghost g t)))
             uu___)
let (core_check_tot_term_with_expected_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.typ -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun t ->
        core_check_term_with_expected_type g e FStar_TypeChecker_Core.E_Total
          t
let (is_non_informative :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp ->
      ((unit, unit) FStar_Tactics_Types.non_informative_token
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (423)) (Prims.of_int (21))
                 (Prims.of_int (423)) (Prims.of_int (89)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (422)) (Prims.of_int (28))
                 (Prims.of_int (425)) (Prims.of_int (6)))))
        (Obj.magic
           (catch_all
              (fun uu___ ->
                 FStar_Tactics_V2_Builtins.is_non_informative
                   (Pulse_Typing.elab_env g)
                   (Pulse_Elaborate_Pure.elab_comp c))))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (ropt, issues) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (424)) (Prims.of_int (2))
                                (Prims.of_int (424)) (Prims.of_int (21)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (423)) (Prims.of_int (6))
                                (Prims.of_int (423)) (Prims.of_int (10)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Builtins.log_issues issues))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> ropt)))) uu___)
let (check_subtyping :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        ((unit, unit, unit) Pulse_Typing.subtyping_token, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_V2_Derived.with_policy FStar_Tactics_Types.SMTSync
          (fun uu___ ->
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (429)) (Prims.of_int (20))
                        (Prims.of_int (429)) (Prims.of_int (47)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (428)) (Prims.of_int (34))
                        (Prims.of_int (437)) (Prims.of_int (47)))))
               (Obj.magic (rtb_check_subtyping g t1 t2))
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
                                       (Prims.of_int (430))
                                       (Prims.of_int (2))
                                       (Prims.of_int (430))
                                       (Prims.of_int (21)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (431))
                                       (Prims.of_int (2))
                                       (Prims.of_int (437))
                                       (Prims.of_int (47)))))
                              (Obj.magic
                                 (FStar_Tactics_V2_Builtins.log_issues issues))
                              (fun uu___2 ->
                                 (fun uu___2 ->
                                    match res with
                                    | FStar_Pervasives_Native.Some tok ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___3 -> tok)))
                                    | FStar_Pervasives_Native.None ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Pure.fst"
                                                         (Prims.of_int (436))
                                                         (Prims.of_int (10))
                                                         (Prims.of_int (437))
                                                         (Prims.of_int (47)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Pure.fst"
                                                         (Prims.of_int (435))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (437))
                                                         (Prims.of_int (47)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (436))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (437))
                                                               (Prims.of_int (46)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (436))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (437))
                                                               (Prims.of_int (47)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (46)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (46)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (21)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (46)))))
                                                                  (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.uu___44
                                                                    t1))
                                                                  (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.uu___44
                                                                    t2))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "and")
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___3
                                                                    uu___4))))
                                                                    uu___3)))
                                                            (fun uu___3 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___4
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Could not prove subtyping of ")
                                                                    uu___3))))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              [uu___3]))))
                                                (fun uu___3 ->
                                                   (fun uu___3 ->
                                                      Obj.magic
                                                        (maybe_fail_doc
                                                           issues g
                                                           t1.Pulse_Syntax_Base.range1
                                                           uu___3)) uu___3))))
                                   uu___2))) uu___1))
let (check_equiv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        ((unit, unit, unit) FStar_Tactics_Types.equiv_token
           FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (442)) (Prims.of_int (4))
                   (Prims.of_int (442)) (Prims.of_int (80)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (440)) (Prims.of_int (25))
                   (Prims.of_int (444)) (Prims.of_int (5)))))
          (Obj.magic
             (Pulse_Typing_Util.check_equiv_now (Pulse_Typing.elab_env g)
                (Pulse_Elaborate_Pure.elab_term t1)
                (Pulse_Elaborate_Pure.elab_term t2)))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | (res, issues) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (443)) (Prims.of_int (2))
                                  (Prims.of_int (443)) (Prims.of_int (21)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (441)) (Prims.of_int (6))
                                  (Prims.of_int (441)) (Prims.of_int (9)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.log_issues issues))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 -> res)))) uu___)