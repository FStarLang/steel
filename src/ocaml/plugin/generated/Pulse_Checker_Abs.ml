open Prims
let (check_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Checker_Common.post_hint_opt ->
            Pulse_Checker_Common.check_t ->
              ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun check ->
              if FStar_Pervasives_Native.uu___is_Some post_hint
              then
                Pulse_Typing_Env.fail g FStar_Pervasives_Native.None
                  "Unexpected post-condition annotation from context for an abstraction"
              else
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                           (Prims.of_int (24)) (Prims.of_int (14))
                           (Prims.of_int (24)) (Prims.of_int (21)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                           (Prims.of_int (25)) (Prims.of_int (2))
                           (Prims.of_int (59)) (Prims.of_int (27)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 -> t.Pulse_Syntax_Base.range2))
                  (fun uu___1 ->
                     (fun range ->
                        match t.Pulse_Syntax_Base.term1 with
                        | Pulse_Syntax_Base.Tm_Abs
                            {
                              Pulse_Syntax_Base.b =
                                { Pulse_Syntax_Base.binder_ty = t1;
                                  Pulse_Syntax_Base.binder_ppname = ppname;_};
                              Pulse_Syntax_Base.q = qual;
                              Pulse_Syntax_Base.pre1 = pre_hint;
                              Pulse_Syntax_Base.body = body;
                              Pulse_Syntax_Base.ret_ty = ret_ty;
                              Pulse_Syntax_Base.post1 = post_hint_body;_}
                            ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Abs.fst"
                                          (Prims.of_int (28))
                                          (Prims.of_int (24))
                                          (Prims.of_int (28))
                                          (Prims.of_int (38)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Abs.fst"
                                          (Prims.of_int (26))
                                          (Prims.of_int (113))
                                          (Prims.of_int (59))
                                          (Prims.of_int (27)))))
                                 (Obj.magic
                                    (Pulse_Checker_Pure.check_term g t1))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       match uu___1 with
                                       | FStar_Pervasives.Mkdtuple3
                                           (t2, uu___2, uu___3) ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Abs.fst"
                                                         (Prims.of_int (29))
                                                         (Prims.of_int (28))
                                                         (Prims.of_int (29))
                                                         (Prims.of_int (46)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Abs.fst"
                                                         (Prims.of_int (28))
                                                         (Prims.of_int (41))
                                                         (Prims.of_int (59))
                                                         (Prims.of_int (27)))))
                                                (Obj.magic
                                                   (Pulse_Checker_Pure.check_universe
                                                      g t2))
                                                (fun uu___4 ->
                                                   (fun uu___4 ->
                                                      match uu___4 with
                                                      | Prims.Mkdtuple2
                                                          (u, t_typing) ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (19)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___5
                                                                    ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g))
                                                               (fun uu___5 ->
                                                                  (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (ppname,
                                                                    x)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    ppname t2))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                                    (match pre_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Cannot typecheck an function without a precondition"))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    pre_hint1
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    pre_hint1
                                                                    px))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    pre_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop
                                                                    g'
                                                                    pre_opened))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (pre_opened1,
                                                                    pre_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.close_term
                                                                    pre_opened1
                                                                    x))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun pre1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Pure.tm_var
                                                                    {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    = ppname
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun var
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.open_term_opt'
                                                                    ret_ty
                                                                    var
                                                                    Prims.int_zero))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    ret_ty1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.open_term_opt'
                                                                    post_hint_body
                                                                    var
                                                                    Prims.int_one))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    post_hint_body1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                                    (match post_hint_body1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (103)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.intro_post_hint
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "post_hint_typing"
                                                                    range g')
                                                                    ret_ty1
                                                                    post))
                                                                    (fun
                                                                    post_hint_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    post_hint_typing)))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (104)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body px)
                                                                    pre_opened1
                                                                    () post))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body',
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname
                                                                    };
                                                                    Pulse_Syntax_Base.q
                                                                    = qual;
                                                                    Pulse_Syntax_Base.pre1
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body' x);
                                                                    Pulse_Syntax_Base.ret_ty
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.post1
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    (Pulse_Syntax_Pure.tm_arrow
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname
                                                                    } qual
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c_body x))),
                                                                    (Pulse_Typing.T_Abs
                                                                    (g, x,
                                                                    qual,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname
                                                                    }, u,
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body' x),
                                                                    c_body,
                                                                    (),
                                                                    body_typing)))))))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                     uu___4))) uu___1)))
                       uu___1)