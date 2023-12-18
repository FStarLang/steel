open Prims
let (check_core :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun st ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                         (Prims.of_int (22)) (Prims.of_int (10))
                         (Prims.of_int (22)) (Prims.of_int (48)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                         (Prims.of_int (22)) (Prims.of_int (51))
                         (Prims.of_int (69)) (Prims.of_int (83)))))
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
                                    (Prims.of_int (23)) (Prims.of_int (53))
                                    (Prims.of_int (23)) (Prims.of_int (60)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Return.fst"
                                    (Prims.of_int (22)) (Prims.of_int (51))
                                    (Prims.of_int (69)) (Prims.of_int (83)))))
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
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (39))
                                                   (Prims.of_int (48)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Return.fst"
                                                   (Prims.of_int (23))
                                                   (Prims.of_int (63))
                                                   (Prims.of_int (69))
                                                   (Prims.of_int (83)))))
                                          (match post_hint with
                                           | FStar_Pervasives_Native.None ->
                                               Obj.magic
                                                 (Pulse_Checker_Pure.compute_tot_term_type_and_u
                                                    g1 t)
                                           | FStar_Pervasives_Native.Some
                                               post ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Return.fst"
                                                             (Prims.of_int (33))
                                                             (Prims.of_int (23))
                                                             (Prims.of_int (33))
                                                             (Prims.of_int (53)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Return.fst"
                                                             (Prims.of_int (32))
                                                             (Prims.of_int (18))
                                                             (Prims.of_int (39))
                                                             (Prims.of_int (48)))))
                                                    (Obj.magic
                                                       (Pulse_Checker_Pure.check_tot_term
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
                                                                    (), ())))))
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
                                                                  (Prims.of_int (40))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (69))
                                                                  (Prims.of_int (83)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Return.fst"
                                                                  (Prims.of_int (40))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (69))
                                                                  (Prims.of_int (83)))))
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
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (83)))))
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
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (res_ppname,
                                                                    x)))
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
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (83)))))
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
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_tot_term
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
                                                                    (Prims.of_int (59))
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
                                                                    "check_return: unexpected variable clash in return post,please file a bug report"))
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
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (83)))))
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
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (83)))))
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
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (83)))))
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
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (83)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g1
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    c)
                                                                    (Pulse_Syntax_Base.Tm_Return
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    = c;
                                                                    Pulse_Syntax_Base.insert_eq
                                                                    = use_eq;
                                                                    Pulse_Syntax_Base.term
                                                                    = t1
                                                                    }))
                                                                    (Pulse_Typing.comp_return
                                                                    c use_eq
                                                                    u ty t1
                                                                    post x)
                                                                    d1
                                                                    post_hint))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun dd
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (83)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.debug
                                                                    g1
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    dd))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (uu___7,
                                                                    c1,
                                                                    uu___8)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c1))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "Return comp is: "
                                                                    (Prims.strcat
                                                                    uu___9 "")))))
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (83)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    g1 ctxt
                                                                    () dd
                                                                    res_ppname))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g1 ctxt
                                                                    uu___6
                                                                    post_hint
                                                                    t1.Pulse_Syntax_Base.range1))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                              uu___2)))
                                               uu___1))) uu___))) uu___)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Checker_Base.check_t ->
                ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun st ->
              fun check1 ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                           (Prims.of_int (80)) (Prims.of_int (22))
                           (Prims.of_int (80)) (Prims.of_int (29)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                           (Prims.of_int (80)) (Prims.of_int (3))
                           (Prims.of_int (94)) (Prims.of_int (5)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> st.Pulse_Syntax_Base.term1))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | Pulse_Syntax_Base.Tm_Return f ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Return.fst"
                                          (Prims.of_int (81))
                                          (Prims.of_int (10))
                                          (Prims.of_int (81))
                                          (Prims.of_int (61)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Return.fst"
                                          (Prims.of_int (81))
                                          (Prims.of_int (4))
                                          (Prims.of_int (94))
                                          (Prims.of_int (5)))))
                                 (Obj.magic
                                    (Pulse_Checker_Base.is_stateful_application
                                       g f.Pulse_Syntax_Base.term))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       match uu___1 with
                                       | FStar_Pervasives_Native.Some st_app
                                           ->
                                           Obj.magic
                                             (check1 g ctxt () post_hint
                                                res_ppname st_app)
                                       | FStar_Pervasives_Native.None ->
                                           (match post_hint with
                                            | FStar_Pervasives_Native.Some
                                                { Pulse_Typing.g = uu___2;
                                                  Pulse_Typing.ctag_hint =
                                                    FStar_Pervasives_Native.Some
                                                    ct;
                                                  Pulse_Typing.ret_ty =
                                                    uu___3;
                                                  Pulse_Typing.u = uu___4;
                                                  Pulse_Typing.ty_typing =
                                                    uu___5;
                                                  Pulse_Typing.post = uu___6;
                                                  Pulse_Typing.x = uu___7;
                                                  Pulse_Typing.post_typing_src
                                                    = uu___8;
                                                  Pulse_Typing.post_typing =
                                                    uu___9;_}
                                                ->
                                                if
                                                  ct =
                                                    f.Pulse_Syntax_Base.ctag
                                                then
                                                  Obj.magic
                                                    (check_core g ctxt ()
                                                       post_hint res_ppname
                                                       st)
                                                else
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Return.fst"
                                                                (Prims.of_int (90))
                                                                (Prims.of_int (24))
                                                                (Prims.of_int (90))
                                                                (Prims.of_int (67)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Return.fst"
                                                                (Prims.of_int (91))
                                                                (Prims.of_int (13))
                                                                (Prims.of_int (91))
                                                                (Prims.of_int (66)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___11 ->
                                                             {
                                                               Pulse_Syntax_Base.term1
                                                                 =
                                                                 (Pulse_Syntax_Base.Tm_Return
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    = ct;
                                                                    Pulse_Syntax_Base.insert_eq
                                                                    =
                                                                    (f.Pulse_Syntax_Base.insert_eq);
                                                                    Pulse_Syntax_Base.term
                                                                    =
                                                                    (f.Pulse_Syntax_Base.term)
                                                                    });
                                                               Pulse_Syntax_Base.range2
                                                                 =
                                                                 (st.Pulse_Syntax_Base.range2);
                                                               Pulse_Syntax_Base.effect_tag
                                                                 =
                                                                 (st.Pulse_Syntax_Base.effect_tag)
                                                             }))
                                                       (fun uu___11 ->
                                                          (fun st1 ->
                                                             Obj.magic
                                                               (check_core g
                                                                  ctxt ()
                                                                  post_hint
                                                                  res_ppname
                                                                  st1))
                                                            uu___11))
                                            | uu___2 ->
                                                Obj.magic
                                                  (check_core g ctxt ()
                                                     post_hint res_ppname st)))
                                      uu___1))) uu___)