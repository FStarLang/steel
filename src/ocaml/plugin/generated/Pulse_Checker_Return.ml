open Prims
let (check_return :
  Prims.bool ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Typing.post_hint_opt ->
              ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun st ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                         (Prims.of_int (23)) (Prims.of_int (10))
                         (Prims.of_int (23)) (Prims.of_int (48)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                         (Prims.of_int (23)) (Prims.of_int (51))
                         (Prims.of_int (62)) (Prims.of_int (68)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Checker_Pure.push_context "check_return"
                        st.Pulse_Syntax_Base.range2 g))
                (fun uu___ ->
                   (fun g1 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Return.fst"
                                    (Prims.of_int (24)) (Prims.of_int (53))
                                    (Prims.of_int (24)) (Prims.of_int (60)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Return.fst"
                                    (Prims.of_int (23)) (Prims.of_int (51))
                                    (Prims.of_int (62)) (Prims.of_int (68)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> st.Pulse_Syntax_Base.term1))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | Pulse_Syntax_Base.Tm_Return
                                     { Pulse_Syntax_Base.ctag = c;
                                       Pulse_Syntax_Base.insert_eq = use_eq;
                                       Pulse_Syntax_Base.term = t;_}
                                     ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Return.fst"
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (40))
                                                   (Prims.of_int (48)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Return.fst"
                                                   (Prims.of_int (24))
                                                   (Prims.of_int (63))
                                                   (Prims.of_int (62))
                                                   (Prims.of_int (68)))))
                                          (match post_hint with
                                           | FStar_Pervasives_Native.None ->
                                               Obj.magic
                                                 (Pulse_Checker_Pure.check_term_and_type
                                                    g1 t)
                                           | FStar_Pervasives_Native.Some
                                               post ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Return.fst"
                                                             (Prims.of_int (34))
                                                             (Prims.of_int (23))
                                                             (Prims.of_int (34))
                                                             (Prims.of_int (68)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Return.fst"
                                                             (Prims.of_int (33))
                                                             (Prims.of_int (18))
                                                             (Prims.of_int (40))
                                                             (Prims.of_int (48)))))
                                                    (Obj.magic
                                                       (Pulse_Checker_Pure.check_term_with_expected_type
                                                          g1 t
                                                          post.Pulse_Typing.ret_ty))
                                                    (fun uu___1 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___2 ->
                                                            match uu___1 with
                                                            | Prims.Mkdtuple2
                                                                (t1, d) ->
                                                                FStar_Pervasives.Mkdtuple5
                                                                  (t1,
                                                                    (
                                                                    post.Pulse_Typing.u),
                                                                    (
                                                                    post.Pulse_Typing.ret_ty),
                                                                    (), d)))))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple5
                                                    (t1, u, ty, uty, d) ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Return.fst"
                                                                  (Prims.of_int (41))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (62))
                                                                  (Prims.of_int (68)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Return.fst"
                                                                  (Prims.of_int (41))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (62))
                                                                  (Prims.of_int (68)))))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               uu___1))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (17)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (68)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Base.v_as_nv
                                                                    x))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (68)))))
                                                                    (match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px) ty)
                                                                    Pulse_Syntax_Base.tm_emp
                                                                    Pulse_Syntax_Base.tm_vprop))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (t2, ty1)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (t2, ()))))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    post))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    post1 ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    post1.Pulse_Typing.post)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Unexpected variable clash in return"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Naming.open_term_nv
                                                                    post1.Pulse_Typing.post
                                                                    px), ())))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_Return
                                                                    (g1, c,
                                                                    use_eq,
                                                                    u, ty,
                                                                    t1, post,
                                                                    x, (),
                                                                    (), ())))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (68)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Return
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    = c;
                                                                    Pulse_Syntax_Base.insert_eq
                                                                    = use_eq;
                                                                    Pulse_Syntax_Base.term
                                                                    = t1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_return
                                                                    c use_eq
                                                                    u ty t1
                                                                    post x)
                                                                    d1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.repack
                                                                    g pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Return
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    = c;
                                                                    Pulse_Syntax_Base.insert_eq
                                                                    = use_eq;
                                                                    Pulse_Syntax_Base.term
                                                                    = t1
                                                                    }))
                                                                    uu___5
                                                                    post_hint))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                              uu___2)))
                                               uu___1))) uu___))) uu___)