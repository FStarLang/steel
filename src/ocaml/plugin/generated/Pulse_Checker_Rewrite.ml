open Prims
let (check_rewrite :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Checker_Common.post_hint_opt ->
            ((unit, unit, unit) Pulse_Checker_Common.checker_result_t, 
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Rewrite.fst"
                       (Prims.of_int (20)) (Prims.of_int (10))
                       (Prims.of_int (20)) (Prims.of_int (40)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Rewrite.fst"
                       (Prims.of_int (20)) (Prims.of_int (43))
                       (Prims.of_int (33)) (Prims.of_int (72)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Pulse_Checker_Pure.push_context "check_rewrite" g))
              (fun uu___ ->
                 (fun g1 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Rewrite.fst"
                                  (Prims.of_int (21)) (Prims.of_int (32))
                                  (Prims.of_int (21)) (Prims.of_int (38)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Rewrite.fst"
                                  (Prims.of_int (20)) (Prims.of_int (43))
                                  (Prims.of_int (33)) (Prims.of_int (72)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> t.Pulse_Syntax_Base.term1))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | Pulse_Syntax_Base.Tm_Rewrite
                                   { Pulse_Syntax_Base.t1 = p;
                                     Pulse_Syntax_Base.t2 = q;_}
                                   ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Rewrite.fst"
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (26))
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (41)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Rewrite.fst"
                                                 (Prims.of_int (21))
                                                 (Prims.of_int (41))
                                                 (Prims.of_int (33))
                                                 (Prims.of_int (72)))))
                                        (Obj.magic
                                           (Pulse_Checker_Pure.check_vprop g1
                                              p))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | Prims.Mkdtuple2
                                                  (p1, p_typing) ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Rewrite.fst"
                                                                (Prims.of_int (23))
                                                                (Prims.of_int (26))
                                                                (Prims.of_int (23))
                                                                (Prims.of_int (41)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Rewrite.fst"
                                                                (Prims.of_int (22))
                                                                (Prims.of_int (44))
                                                                (Prims.of_int (33))
                                                                (Prims.of_int (72)))))
                                                       (Obj.magic
                                                          (Pulse_Checker_Pure.check_vprop
                                                             g1 q))
                                                       (fun uu___2 ->
                                                          (fun uu___2 ->
                                                             match uu___2
                                                             with
                                                             | Prims.Mkdtuple2
                                                                 (q1,
                                                                  q_typing)
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (72)))))
                                                                    (if
                                                                    Pulse_Syntax_Base.eq_tm
                                                                    p1 q1
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ())))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.check_equiv
                                                                    (Pulse_Typing.elab_env
                                                                    g1)
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    p1)
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    q1)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    issues)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.print_issues
                                                                    g1 issues))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "rewrite: p and q elabs are not equiv\n"
                                                                    (Prims.strcat
                                                                    uu___5 "")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    uu___5)))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    token,
                                                                    uu___5)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    ()))))
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    equiv_p_q
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Rewrite
                                                                    (g1, p1,
                                                                    q1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (72)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t1
                                                                    = p1;
                                                                    Pulse_Syntax_Base.t2
                                                                    = q1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_rewrite
                                                                    p1 q1) d))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.repack
                                                                    g pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t1
                                                                    = p1;
                                                                    Pulse_Syntax_Base.t2
                                                                    = q1
                                                                    }))
                                                                    uu___3
                                                                    post_hint))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                            uu___2))) uu___1)))
                              uu___))) uu___)