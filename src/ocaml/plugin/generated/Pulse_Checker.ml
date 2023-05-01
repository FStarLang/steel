open Prims
let (terms_to_string :
  Pulse_Syntax.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (21))
         (Prims.of_int (23)) (Prims.of_int (21)) (Prims.of_int (68)))
      (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (21))
         (Prims.of_int (4)) (Prims.of_int (21)) (Prims.of_int (68)))
      (Obj.magic
         (FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_String.concat "\n" uu___))
exception Framing_failure of Pulse_Checker_Framing.framing_failure 
let (uu___is_Framing_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Framing_failure uu___ -> true | uu___ -> false
let (__proj__Framing_failure__item__uu___ :
  Prims.exn -> Pulse_Checker_Framing.framing_failure) =
  fun projectee -> match projectee with | Framing_failure uu___ -> uu___
let (try_frame_pre :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        Pulse_Syntax.term ->
          unit ->
            Pulse_Syntax.comp_st ->
              (unit, unit, unit, unit) Pulse_Typing.st_typing ->
                ((Pulse_Syntax.comp_st,
                   (unit, unit, unit, unit) Pulse_Typing.st_typing)
                   Prims.dtuple2,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun c ->
              fun t_typing ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (34)) (Prims.of_int (10))
                     (Prims.of_int (34)) (Prims.of_int (65)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (34)) (Prims.of_int (4))
                     (Prims.of_int (36)) (Prims.of_int (48)))
                  (Obj.magic
                     (Pulse_Checker_Framing.try_frame_pre f g t pre () c
                        t_typing))
                  (fun uu___ ->
                     match uu___ with
                     | FStar_Pervasives.Inl ok ->
                         FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ok)
                     | FStar_Pervasives.Inr fail ->
                         FStar_Tactics_Effect.raise (Framing_failure fail))
let (replace_equiv_post :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.comp ->
        Pulse_Syntax.term FStar_Pervasives_Native.option ->
          ((Pulse_Syntax.comp,
             (unit, unit, unit, unit) Pulse_Typing.st_equiv) Prims.dtuple2,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun c ->
        fun post_hint ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (47))
               (Prims.of_int (48)) (Prims.of_int (47)) (Prims.of_int (65)))
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (47))
               (Prims.of_int (2)) (Prims.of_int (92)) (Prims.of_int (5)))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_Syntax.st_comp_of_comp c))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | { Pulse_Syntax.u = u_c; Pulse_Syntax.res = res_c;
                      Pulse_Syntax.pre = pre_c; Pulse_Syntax.post = post_c;_}
                      ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (48)) (Prims.of_int (10))
                              (Prims.of_int (48)) (Prims.of_int (17)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (49)) (Prims.of_int (2))
                              (Prims.of_int (92)) (Prims.of_int (5)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> Pulse_Typing.fresh g))
                           (fun uu___1 ->
                              (fun x ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (49))
                                         (Prims.of_int (29))
                                         (Prims.of_int (49))
                                         (Prims.of_int (31)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (51))
                                         (Prims.of_int (2))
                                         (Prims.of_int (92))
                                         (Prims.of_int (5)))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            (x, (FStar_Pervasives.Inl res_c))
                                            :: g))
                                      (fun uu___1 ->
                                         (fun g_post ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.fst"
                                                    (Prims.of_int (52))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (52))
                                                    (Prims.of_int (35)))
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.fst"
                                                    (Prims.of_int (53))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (92))
                                                    (Prims.of_int (5)))
                                                 (Obj.magic
                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                       f g pre_c))
                                                 (fun uu___1 ->
                                                    (fun pre_c_typing ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.fst"
                                                               (Prims.of_int (54))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (57))
                                                               (Prims.of_int (84)))
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.fst"
                                                               (Prims.of_int (58))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (92))
                                                               (Prims.of_int (5)))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (46)))
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (84)))
                                                                  (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    f g res_c))
                                                                  (fun uu___1
                                                                    ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u, ty)
                                                                    ->
                                                                    if
                                                                    u = u_c
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ())
                                                                    else
                                                                    FStar_Tactics_Derived.fail
                                                                    "T_Abs: re-typechecking the return type returned different universe")))
                                                            (fun uu___1 ->
                                                               (fun
                                                                  res_c_typing
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (5)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax.open_term
                                                                    post_c x))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    post_c_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    f g_post
                                                                    post_c_opened))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    post_c_typing
                                                                    ->
                                                                    match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    (Pulse_Typing.ST_VPropEquiv
                                                                    (g, c, c,
                                                                    x, (),
                                                                    (), (),
                                                                    (), ()))))))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax.freevars
                                                                    post)
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Unexpected variable clash with annotated postcondition")
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (27)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax.open_term
                                                                    post x))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    post_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (75)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (27)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop
                                                                    f g_post
                                                                    post_opened))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened1,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (74)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (27)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Framing.check_vprop_equiv
                                                                    f g_post
                                                                    post_c_opened
                                                                    post_opened1
                                                                    ()))
                                                                    (fun
                                                                    post_c_post_eq
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax.with_st_comp
                                                                    c
                                                                    {
                                                                    Pulse_Syntax.u
                                                                    = u_c;
                                                                    Pulse_Syntax.res
                                                                    = res_c;
                                                                    Pulse_Syntax.pre
                                                                    = pre_c;
                                                                    Pulse_Syntax.post
                                                                    =
                                                                    (Pulse_Syntax.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }),
                                                                    (Pulse_Typing.ST_VPropEquiv
                                                                    (g, c,
                                                                    (Pulse_Syntax.with_st_comp
                                                                    c
                                                                    {
                                                                    Pulse_Syntax.u
                                                                    = u_c;
                                                                    Pulse_Syntax.res
                                                                    = res_c;
                                                                    Pulse_Syntax.pre
                                                                    = pre_c;
                                                                    Pulse_Syntax.post
                                                                    =
                                                                    (Pulse_Syntax.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }), x,
                                                                    (), (),
                                                                    (), (),
                                                                    ())))))))
                                                                    uu___2)))
                                                                    uu___2)))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                 uu___1)))
                                                      uu___1))) uu___1)))
                                uu___1))) uu___)
let (check_abs :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        Pulse_Syntax.term ->
          unit ->
            Pulse_Syntax.term FStar_Pervasives_Native.option ->
              Pulse_Checker_Common.check_t ->
                ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                   (unit, unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun check ->
                match t with
                | Pulse_Syntax.Tm_Abs
                    ({ Pulse_Syntax.binder_ty = t1;
                       Pulse_Syntax.binder_ppname = ppname;_},
                     qual, pre_hint, body, post_hint1)
                    ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (109)) (Prims.of_int (24))
                         (Prims.of_int (109)) (Prims.of_int (39)))
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (109)) (Prims.of_int (4))
                         (Prims.of_int (137)) (Prims.of_int (28)))
                      (Obj.magic (Pulse_Checker_Pure.check_tot f g t1))
                      (fun uu___ ->
                         (fun uu___ ->
                            match uu___ with
                            | FStar_Pervasives.Mkdtuple3 (t2, uu___1, uu___2)
                                ->
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (110))
                                        (Prims.of_int (28))
                                        (Prims.of_int (110))
                                        (Prims.of_int (48)))
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (110))
                                        (Prims.of_int (4))
                                        (Prims.of_int (137))
                                        (Prims.of_int (28)))
                                     (Obj.magic
                                        (Pulse_Checker_Pure.check_universe f
                                           g t2))
                                     (fun uu___3 ->
                                        (fun uu___3 ->
                                           match uu___3 with
                                           | Prims.Mkdtuple2 (u, t_typing) ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (111))
                                                       (Prims.of_int (12))
                                                       (Prims.of_int (111))
                                                       (Prims.of_int (19)))
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (112))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (137))
                                                       (Prims.of_int (28)))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___4 ->
                                                          Pulse_Typing.fresh
                                                            g))
                                                    (fun uu___4 ->
                                                       (fun x ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (112))
                                                                  (Prims.of_int (24))
                                                                  (Prims.of_int (112))
                                                                  (Prims.of_int (26)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (113))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (137))
                                                                  (Prims.of_int (28)))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives.Inl
                                                                    t2)) :: g))
                                                               (fun uu___4 ->
                                                                  (fun g' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (28)))
                                                                    (match pre_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "Cannot typecheck an function without a precondition"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    pre_hint1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax.open_term
                                                                    pre_hint1
                                                                    x))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pre_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (28)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_tot
                                                                    f g'
                                                                    pre_opened))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (pre_opened1,
                                                                    Pulse_Syntax.Tm_VProp,
                                                                    pre_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (14)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax.close_term
                                                                    pre_opened1
                                                                    x))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun pre1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (19)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (14)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match post_hint1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.open_term'
                                                                    post
                                                                    (Pulse_Syntax.Tm_Var
                                                                    {
                                                                    Pulse_Syntax.nm_index
                                                                    = x;
                                                                    Pulse_Syntax.nm_ppname
                                                                    =
                                                                    FStar_Reflection_Typing.pp_name_default
                                                                    })
                                                                    Prims.int_one)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (108)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (14)))
                                                                    (Obj.magic
                                                                    (check f
                                                                    g'
                                                                    (Pulse_Syntax.open_st_term
                                                                    body x)
                                                                    pre_opened1
                                                                    () post))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body',
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax.Tm_Abs
                                                                    ({
                                                                    Pulse_Syntax.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax.binder_ppname
                                                                    = ppname
                                                                    }, qual,
                                                                    FStar_Pervasives_Native.None,
                                                                    (Pulse_Syntax.close_st_term
                                                                    body' x),
                                                                    FStar_Pervasives_Native.None)),
                                                                    (Pulse_Syntax.C_Tot
                                                                    (Pulse_Syntax.Tm_Arrow
                                                                    ({
                                                                    Pulse_Syntax.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax.binder_ppname
                                                                    = ppname
                                                                    }, qual,
                                                                    (Pulse_Syntax.close_comp
                                                                    c_body x)))),
                                                                    (Pulse_Typing.T_Abs
                                                                    (g, x,
                                                                    qual, t2,
                                                                    u,
                                                                    (Pulse_Syntax.close_st_term
                                                                    body' x),
                                                                    c_body,
                                                                    (),
                                                                    body_typing)))))))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "bad hint")))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                         uu___4))) uu___3)))
                           uu___)
let (has_pure_vprops : Pulse_Syntax.term -> Prims.bool) =
  fun pre ->
    FStar_List_Tot_Base.existsb Pulse_Syntax.uu___is_Tm_Pure
      (Pulse_Checker_Framing.vprop_as_list pre)
let (elim_pure_explicit_lid : Prims.string Prims.list) =
  Pulse_Reflection_Util.mk_steel_wrapper_lid "elim_pure_explicit"
let (maybe_add_elim_pure :
  Pulse_Syntax.term Prims.list ->
    Pulse_Syntax.st_term ->
      ((Prims.bool * Pulse_Syntax.st_term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun pre ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   if
                     (FStar_List_Tot_Base.length
                        (FStar_List_Tot_Base.flatten
                           (FStar_List_Tot_Base.map
                              (fun t1 ->
                                 match t1 with
                                 | Pulse_Syntax.Tm_Pure p -> [p]
                                 | uu___1 -> []) pre)))
                       = Prims.int_zero
                   then (false, t)
                   else
                     (true,
                       (FStar_List_Tot_Base.fold_left
                          (fun t1 ->
                             fun p ->
                               Pulse_Syntax.Tm_Bind
                                 ((Pulse_Syntax.Tm_Protect
                                     (Pulse_Syntax.Tm_STApp
                                        ((Pulse_Syntax.Tm_FVar
                                            elim_pure_explicit_lid),
                                          FStar_Pervasives_Native.None, p))),
                                   t1)) t
                          (FStar_List_Tot_Base.flatten
                             (FStar_List_Tot_Base.map
                                (fun t1 ->
                                   match t1 with
                                   | Pulse_Syntax.Tm_Pure p -> [p]
                                   | uu___2 -> []) pre))))))) uu___1 uu___
let rec (combine_if_branches :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        Pulse_Syntax.comp_st ->
          (unit, unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Typing.env ->
              Pulse_Syntax.st_term ->
                Pulse_Syntax.comp_st ->
                  (unit, unit, unit, unit) Pulse_Typing.st_typing ->
                    ((Pulse_Syntax.comp_st,
                       (unit, unit, unit, unit) Pulse_Typing.st_typing,
                       (unit, unit, unit, unit) Pulse_Typing.st_typing)
                       FStar_Pervasives.dtuple3,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___8 ->
    fun uu___7 ->
      fun uu___6 ->
        fun uu___5 ->
          fun uu___4 ->
            fun uu___3 ->
              fun uu___2 ->
                fun uu___1 ->
                  fun uu___ ->
                    (fun f ->
                       fun g_then ->
                         fun e_then ->
                           fun c_then ->
                             fun e_then_typing ->
                               fun g_else ->
                                 fun e_else ->
                                   fun c_else ->
                                     fun e_else_typing ->
                                       if
                                         Pulse_Syntax.eq_st_comp
                                           (Pulse_Syntax.st_comp_of_comp
                                              c_then)
                                           (Pulse_Syntax.st_comp_of_comp
                                              c_else)
                                       then
                                         Obj.magic
                                           (Obj.repr
                                              (match (c_then, c_else) with
                                               | (Pulse_Syntax.C_ST uu___,
                                                  Pulse_Syntax.C_ST uu___1)
                                                   ->
                                                   Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           FStar_Pervasives.Mkdtuple3
                                                             (c_then,
                                                               e_then_typing,
                                                               e_else_typing)))
                                               | (Pulse_Syntax.C_STAtomic
                                                  (inames1, uu___),
                                                  Pulse_Syntax.C_STAtomic
                                                  (inames2, uu___1)) ->
                                                   Obj.repr
                                                     (if
                                                        Pulse_Syntax.eq_tm
                                                          inames1 inames2
                                                      then
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             FStar_Pervasives.Mkdtuple3
                                                               (c_then,
                                                                 e_then_typing,
                                                                 e_else_typing))
                                                      else
                                                        FStar_Tactics_Derived.fail
                                                          "Cannot combine then and else branches (different inames)")
                                               | (Pulse_Syntax.C_STGhost
                                                  (inames1, uu___),
                                                  Pulse_Syntax.C_STGhost
                                                  (inames2, uu___1)) ->
                                                   Obj.repr
                                                     (if
                                                        Pulse_Syntax.eq_tm
                                                          inames1 inames2
                                                      then
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             FStar_Pervasives.Mkdtuple3
                                                               (c_then,
                                                                 e_then_typing,
                                                                 e_else_typing))
                                                      else
                                                        FStar_Tactics_Derived.fail
                                                          "Cannot combine then and else branches (different inames)")
                                               | (Pulse_Syntax.C_ST uu___,
                                                  Pulse_Syntax.C_STAtomic
                                                  (inames, uu___1)) ->
                                                   Obj.repr
                                                     (if
                                                        Pulse_Syntax.eq_tm
                                                          inames
                                                          Pulse_Syntax.Tm_EmpInames
                                                      then
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             FStar_Pervasives.Mkdtuple3
                                                               (c_then,
                                                                 e_then_typing,
                                                                 (Pulse_Typing.T_Lift
                                                                    (g_else,
                                                                    e_else,
                                                                    c_else,
                                                                    c_then,
                                                                    e_else_typing,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g_else,
                                                                    c_else))))))
                                                      else
                                                        FStar_Tactics_Derived.fail
                                                          "Cannot lift STAtomic else branch to match then")
                                               | (Pulse_Syntax.C_STAtomic
                                                  (inames, uu___),
                                                  Pulse_Syntax.C_ST uu___1)
                                                   ->
                                                   Obj.repr
                                                     (if
                                                        Pulse_Syntax.eq_tm
                                                          inames
                                                          Pulse_Syntax.Tm_EmpInames
                                                      then
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             FStar_Pervasives.Mkdtuple3
                                                               (c_else,
                                                                 (Pulse_Typing.T_Lift
                                                                    (g_then,
                                                                    e_then,
                                                                    c_then,
                                                                    c_else,
                                                                    e_then_typing,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g_then,
                                                                    c_then)))),
                                                                 e_else_typing))
                                                      else
                                                        FStar_Tactics_Derived.fail
                                                          "Cannot lift STAtomic else branch to match then")
                                               | (Pulse_Syntax.C_STGhost
                                                  (uu___, uu___1), uu___2) ->
                                                   Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (208))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (208))
                                                           (Prims.of_int (84)))
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (209))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (213))
                                                           (Prims.of_int (35)))
                                                        (Obj.magic
                                                           (Pulse_Checker_Pure.get_non_informative_witness
                                                              f g_then
                                                              (Pulse_Syntax.comp_u
                                                                 c_then)
                                                              (Pulse_Syntax.comp_res
                                                                 c_then)))
                                                        (fun uu___3 ->
                                                           (fun w ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (66)))
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (35)))
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g_then,
                                                                    e_then,
                                                                    c_then,
                                                                    (Pulse_Syntax.C_STAtomic
                                                                    ((Pulse_Syntax.comp_inames
                                                                    c_then),
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c_then))),
                                                                    e_then_typing,
                                                                    (Pulse_Typing.Lift_STGhost_STAtomic
                                                                    (g_then,
                                                                    c_then,
                                                                    w)))))
                                                                   (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    e_then_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (combine_if_branches
                                                                    f g_then
                                                                    e_then
                                                                    (Pulse_Syntax.C_STAtomic
                                                                    ((Pulse_Syntax.comp_inames
                                                                    c_then),
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c_then)))
                                                                    e_then_typing1
                                                                    g_else
                                                                    e_else
                                                                    c_else
                                                                    e_else_typing))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c,
                                                                    e1_typing,
                                                                    e2_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c,
                                                                    e1_typing,
                                                                    e2_typing)))))
                                                                    uu___3)))
                                                             uu___3))
                                               | (uu___,
                                                  Pulse_Syntax.C_STGhost
                                                  (uu___1, uu___2)) ->
                                                   Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (215))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (215))
                                                           (Prims.of_int (84)))
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (216))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (218))
                                                           (Prims.of_int (67)))
                                                        (Obj.magic
                                                           (Pulse_Checker_Pure.get_non_informative_witness
                                                              f g_else
                                                              (Pulse_Syntax.comp_u
                                                                 c_else)
                                                              (Pulse_Syntax.comp_res
                                                                 c_else)))
                                                        (fun uu___3 ->
                                                           (fun w ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (66)))
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (67)))
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g_else,
                                                                    e_else,
                                                                    c_else,
                                                                    (Pulse_Syntax.C_STAtomic
                                                                    ((Pulse_Syntax.comp_inames
                                                                    c_else),
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c_else))),
                                                                    e_else_typing,
                                                                    (Pulse_Typing.Lift_STGhost_STAtomic
                                                                    (g_else,
                                                                    c_else,
                                                                    w)))))
                                                                   (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    e_else_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (combine_if_branches
                                                                    f g_then
                                                                    e_then
                                                                    c_then
                                                                    e_then_typing
                                                                    g_else
                                                                    e_else
                                                                    (Pulse_Syntax.C_STAtomic
                                                                    ((Pulse_Syntax.comp_inames
                                                                    c_else),
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c_else)))
                                                                    e_else_typing1))
                                                                    uu___3)))
                                                             uu___3))
                                               | (uu___, uu___1) ->
                                                   Obj.repr
                                                     (FStar_Tactics_Derived.fail
                                                        "Cannot combine then and else branches (incompatible effects)")))
                                       else
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Derived.fail
                                                 "Cannot combine then and else branches (different st_comp)")))
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___
let (check_comp :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.comp_st ->
        unit ->
          ((unit, unit, unit, unit) Pulse_Typing.comp_typing, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun c ->
        fun pre_typing ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (235))
               (Prims.of_int (8)) (Prims.of_int (249)) (Prims.of_int (9)))
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (251))
               (Prims.of_int (4)) (Prims.of_int (266)) (Prims.of_int (44)))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  fun st ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (235)) (Prims.of_int (27))
                         (Prims.of_int (235)) (Prims.of_int (52)))
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (235)) (Prims.of_int (8))
                         (Prims.of_int (249)) (Prims.of_int (9)))
                      (Obj.magic
                         (Pulse_Checker_Pure.check_universe f g
                            st.Pulse_Syntax.res))
                      (fun uu___1 ->
                         (fun uu___1 ->
                            match uu___1 with
                            | Prims.Mkdtuple2 (u, t_u) ->
                                if u <> (Pulse_Syntax.comp_u c)
                                then
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Derived.fail
                                          "Unexpected universe"))
                                else
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (239))
                                             (Prims.of_int (18))
                                             (Prims.of_int (239))
                                             (Prims.of_int (25)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (241))
                                             (Prims.of_int (10))
                                             (Prims.of_int (248))
                                             (Prims.of_int (11)))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                Pulse_Typing.fresh g))
                                          (fun uu___3 ->
                                             (fun x ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.fst"
                                                        (Prims.of_int (241))
                                                        (Prims.of_int (34))
                                                        (Prims.of_int (241))
                                                        (Prims.of_int (36)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.fst"
                                                        (Prims.of_int (242))
                                                        (Prims.of_int (10))
                                                        (Prims.of_int (248))
                                                        (Prims.of_int (11)))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 ->
                                                           (x,
                                                             (FStar_Pervasives.Inl
                                                                (st.Pulse_Syntax.res)))
                                                           :: g))
                                                     (fun uu___3 ->
                                                        (fun gx ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.fst"
                                                                   (Prims.of_int (242))
                                                                   (Prims.of_int (38))
                                                                   (Prims.of_int (242))
                                                                   (Prims.of_int (86)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.fst"
                                                                   (Prims.of_int (242))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (248))
                                                                   (Prims.of_int (11)))
                                                                (Obj.magic
                                                                   (Pulse_Checker_Pure.check_with_core
                                                                    f gx
                                                                    (Pulse_Syntax.open_term
                                                                    (Pulse_Syntax.comp_post
                                                                    c) x)))
                                                                (fun uu___3
                                                                   ->
                                                                   match uu___3
                                                                   with
                                                                   | 
                                                                   Prims.Mkdtuple2
                                                                    (ty,
                                                                    post_typing)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax.eq_tm
                                                                    ty
                                                                    Pulse_Syntax.Tm_VProp)
                                                                    then
                                                                    FStar_Tactics_Derived.fail
                                                                    "Ill-typed postcondition"
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.STC
                                                                    (g, st,
                                                                    x, (),
                                                                    (), ())))))
                                                          uu___3))) uu___3))))
                           uu___1)))
            (fun uu___ ->
               (fun check_st_comp ->
                  match c with
                  | Pulse_Syntax.C_ST st ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (253)) (Prims.of_int (16))
                              (Prims.of_int (253)) (Prims.of_int (32)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (254)) (Prims.of_int (6))
                              (Prims.of_int (254)) (Prims.of_int (19)))
                           (Obj.magic (check_st_comp st))
                           (fun stc ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> Pulse_Typing.CT_ST (g, st, stc))))
                  | Pulse_Syntax.C_STAtomic (i, st) ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (256)) (Prims.of_int (16))
                              (Prims.of_int (256)) (Prims.of_int (32)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (257)) (Prims.of_int (6))
                              (Prims.of_int (260)) (Prims.of_int (45)))
                           (Obj.magic (check_st_comp st))
                           (fun uu___ ->
                              (fun stc ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (257))
                                         (Prims.of_int (31))
                                         (Prims.of_int (257))
                                         (Prims.of_int (52)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (257))
                                         (Prims.of_int (6))
                                         (Prims.of_int (260))
                                         (Prims.of_int (45)))
                                      (Obj.magic
                                         (Pulse_Checker_Pure.check_with_core
                                            f g i))
                                      (fun uu___ ->
                                         match uu___ with
                                         | Prims.Mkdtuple2 (ty, i_typing) ->
                                             if
                                               Prims.op_Negation
                                                 (Pulse_Syntax.eq_tm ty
                                                    Pulse_Syntax.Tm_Inames)
                                             then
                                               FStar_Tactics_Derived.fail
                                                 "Ill-typed inames"
                                             else
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    Pulse_Typing.CT_STAtomic
                                                      (g, i, st, (), stc)))))
                                uu___))
                  | Pulse_Syntax.C_STGhost (i, st) ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (262)) (Prims.of_int (16))
                              (Prims.of_int (262)) (Prims.of_int (32)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (263)) (Prims.of_int (6))
                              (Prims.of_int (266)) (Prims.of_int (44)))
                           (Obj.magic (check_st_comp st))
                           (fun uu___ ->
                              (fun stc ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (263))
                                         (Prims.of_int (31))
                                         (Prims.of_int (263))
                                         (Prims.of_int (52)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (263))
                                         (Prims.of_int (6))
                                         (Prims.of_int (266))
                                         (Prims.of_int (44)))
                                      (Obj.magic
                                         (Pulse_Checker_Pure.check_with_core
                                            f g i))
                                      (fun uu___ ->
                                         match uu___ with
                                         | Prims.Mkdtuple2 (ty, i_typing) ->
                                             if
                                               Prims.op_Negation
                                                 (Pulse_Syntax.eq_tm ty
                                                    Pulse_Syntax.Tm_Inames)
                                             then
                                               FStar_Tactics_Derived.fail
                                                 "Ill-typed inames"
                                             else
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    Pulse_Typing.CT_STGhost
                                                      (g, i, st, (), stc)))))
                                uu___))) uu___)
let (check_if :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.term ->
        Pulse_Syntax.st_term ->
          Pulse_Syntax.st_term ->
            Pulse_Syntax.term ->
              unit ->
                Pulse_Syntax.term ->
                  Pulse_Checker_Common.check_t ->
                    ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                       (unit, unit, unit, unit) Pulse_Typing.st_typing)
                       FStar_Pervasives.dtuple3,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun b ->
        fun e1 ->
          fun e2 ->
            fun pre ->
              fun pre_typing ->
                fun post ->
                  fun check ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (280)) (Prims.of_int (6))
                         (Prims.of_int (280)) (Prims.of_int (47)))
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (279)) (Prims.of_int (4))
                         (Prims.of_int (315)) (Prims.of_int (78)))
                      (Obj.magic
                         (Pulse_Checker_Pure.check_tot_with_expected_typ f g
                            b Pulse_Typing.tm_bool))
                      (fun uu___ ->
                         (fun uu___ ->
                            match uu___ with
                            | Prims.Mkdtuple2 (b1, b_typing) ->
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (281))
                                        (Prims.of_int (14))
                                        (Prims.of_int (281))
                                        (Prims.of_int (21)))
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (282))
                                        (Prims.of_int (4))
                                        (Prims.of_int (315))
                                        (Prims.of_int (78)))
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 -> Pulse_Typing.fresh g))
                                     (fun uu___1 ->
                                        (fun hyp ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.fst"
                                                   (Prims.of_int (283))
                                                   (Prims.of_int (47))
                                                   (Prims.of_int (283))
                                                   (Prims.of_int (49)))
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.fst"
                                                   (Prims.of_int (285))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (315))
                                                   (Prims.of_int (78)))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___1 ->
                                                      fun eq_v ->
                                                        (hyp,
                                                          (FStar_Pervasives.Inl
                                                             (Pulse_Typing.mk_eq2
                                                                Pulse_Syntax.U_zero
                                                                Pulse_Typing.tm_bool
                                                                b1 eq_v)))
                                                        :: g))
                                                (fun uu___1 ->
                                                   (fun g_with_eq ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.fst"
                                                              (Prims.of_int (289))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (303))
                                                              (Prims.of_int (35)))
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.fst"
                                                              (Prims.of_int (308))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (315))
                                                              (Prims.of_int (78)))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___1 ->
                                                                 fun eq_v ->
                                                                   fun br ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (35)))
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    f
                                                                    g_with_eq1
                                                                    pre))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (check f
                                                                    g_with_eq1
                                                                    br pre ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c,
                                                                    br_typing)
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    hyp
                                                                    (Pulse_Syntax.freevars_st
                                                                    br1)
                                                                    then
                                                                    FStar_Tactics_Derived.fail
                                                                    "Illegal use of control-flow hypothesis in branch"
                                                                    else
                                                                    if
                                                                    Pulse_Syntax.uu___is_C_Tot
                                                                    c
                                                                    then
                                                                    FStar_Tactics_Derived.fail
                                                                    "Branch computation type not st"
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c,
                                                                    br_typing)))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                           (fun uu___1 ->
                                                              (fun
                                                                 check_branch
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    Pulse_Typing.tm_true
                                                                    e1))
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    Pulse_Typing.tm_false
                                                                    e2))
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (combine_if_branches
                                                                    f
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (check_comp
                                                                    f g c ()))
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax.Tm_If
                                                                    (b1, e11,
                                                                    e21,
                                                                    FStar_Pervasives_Native.None)),
                                                                    c,
                                                                    (Pulse_Typing.T_If
                                                                    (g, b1,
                                                                    e11, e21,
                                                                    c,
                                                                    (Pulse_Syntax.comp_u
                                                                    c), hyp,
                                                                    (),
                                                                    e1_typing1,
                                                                    e2_typing1,
                                                                    ())))))))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                                uu___1)))
                                                     uu___1))) uu___1)))
                           uu___)
let (repack :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.term ->
        Pulse_Syntax.st_term ->
          (Pulse_Syntax.comp_st,
            (unit, unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2 ->
            Pulse_Syntax.term FStar_Pervasives_Native.option ->
              Prims.bool ->
                ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                   (unit, unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun pre ->
        fun t ->
          fun x ->
            fun post_hint ->
              fun apply_post_hint ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (326)) (Prims.of_int (21))
                     (Prims.of_int (326)) (Prims.of_int (22)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (326)) (Prims.of_int (2))
                     (Prims.of_int (333)) (Prims.of_int (22)))
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | Prims.Mkdtuple2 (c, d_c) ->
                            if
                              apply_post_hint &&
                                (Pulse_Syntax.stateful_comp c)
                            then
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (330))
                                         (Prims.of_int (28))
                                         (Prims.of_int (330))
                                         (Prims.of_int (62)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (330))
                                         (Prims.of_int (4))
                                         (Prims.of_int (331))
                                         (Prims.of_int (44)))
                                      (Obj.magic
                                         (replace_equiv_post f g c post_hint))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              match uu___1 with
                                              | Prims.Mkdtuple2 (c1, c_c1_eq)
                                                  ->
                                                  FStar_Pervasives.Mkdtuple3
                                                    (t, c1,
                                                      (Pulse_Typing.T_Equiv
                                                         (g, t, c, c1, d_c,
                                                           c_c1_eq)))))))
                            else
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         FStar_Pervasives.Mkdtuple3
                                           (t, c, d_c))))) uu___)
let (check_elim_exists :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        Pulse_Syntax.term ->
          unit ->
            Pulse_Syntax.term FStar_Pervasives_Native.option ->
              ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                 (unit, unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (345)) (Prims.of_int (24))
                   (Prims.of_int (345)) (Prims.of_int (25)))
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (345)) (Prims.of_int (2))
                   (Prims.of_int (374)) (Prims.of_int (56)))
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax.Tm_ElimExists t1 ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (347)) (Prims.of_int (6))
                                  (Prims.of_int (359)) (Prims.of_int (14)))
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (361)) (Prims.of_int (2))
                                  (Prims.of_int (374)) (Prims.of_int (56)))
                               (match t1 with
                                | Pulse_Syntax.Tm_Unknown ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (350))
                                               (Prims.of_int (17))
                                               (Prims.of_int (350))
                                               (Prims.of_int (34)))
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (351))
                                               (Prims.of_int (8))
                                               (Prims.of_int (357))
                                               (Prims.of_int (43)))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  Pulse_Checker_Framing.vprop_as_list
                                                    pre))
                                            (fun uu___1 ->
                                               (fun ts ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (351))
                                                          (Prims.of_int (24))
                                                          (Prims.of_int (351))
                                                          (Prims.of_int (101)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (352))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (357))
                                                          (Prims.of_int (43)))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___1 ->
                                                             FStar_List_Tot_Base.filter
                                                               (fun uu___2 ->
                                                                  match uu___2
                                                                  with
                                                                  | Pulse_Syntax.Tm_ExistsSL
                                                                    (uu___3,
                                                                    uu___4,
                                                                    uu___5,
                                                                    uu___6)
                                                                    -> true
                                                                  | uu___3 ->
                                                                    false) ts))
                                                       (fun uu___1 ->
                                                          (fun exist_tms ->
                                                             match exist_tms
                                                             with
                                                             | one::[] ->
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    one)))
                                                             | uu___1 ->
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (43)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (terms_to_string
                                                                    exist_tms))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Could not decide which exists term to eliminate: choices are\n"
                                                                    (Prims.strcat
                                                                    uu___2 "")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___2))))
                                                            uu___1))) uu___1)))
                                | uu___1 ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 -> t1))))
                               (fun uu___1 ->
                                  (fun t2 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (361))
                                             (Prims.of_int (26))
                                             (Prims.of_int (361))
                                             (Prims.of_int (43)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (361))
                                             (Prims.of_int (2))
                                             (Prims.of_int (374))
                                             (Prims.of_int (56)))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.check_vprop
                                                f g t2))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | Prims.Mkdtuple2
                                                    (t3, t_typing) ->
                                                    (match t3 with
                                                     | Pulse_Syntax.Tm_ExistsSL
                                                         (u, ty, p, uu___2)
                                                         ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (49)))
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (57)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (49)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    t3))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "LOG ELIM EXISTS: "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    "\n")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.print
                                                                    uu___3))
                                                                    uu___3)))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (57)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    f g ty))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u',
                                                                    ty_typing)
                                                                    ->
                                                                    if u = u'
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (24)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_ElimExists
                                                                    (g, u,
                                                                    ty, p, x,
                                                                    (), ())))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (44)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (59)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    f g
                                                                    (Pulse_Syntax.Tm_ElimExists
                                                                    (Pulse_Syntax.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax.should_elim_false)))
                                                                    pre ()
                                                                    (Pulse_Typing.comp_elim_exists
                                                                    u ty p x)
                                                                    d))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (repack f
                                                                    g pre
                                                                    (Pulse_Syntax.Tm_ElimExists
                                                                    (Pulse_Syntax.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax.should_elim_false)))
                                                                    uu___5
                                                                    post_hint
                                                                    true))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Universe checking failed in elim_exists")))
                                                                    uu___4)))
                                                                    uu___3)))
                                                     | uu___2 ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Derived.fail
                                                                 "elim_exists argument not a Tm_ExistsSL"))))
                                               uu___1))) uu___1))) uu___)
let (is_intro_exists_erased : Pulse_Syntax.st_term -> Prims.bool) =
  fun st ->
    match st with
    | Pulse_Syntax.Tm_IntroExists (e, uu___, uu___1) -> e
    | uu___ -> false
let (intro_exists_vprop : Pulse_Syntax.st_term -> Pulse_Syntax.vprop) =
  fun st ->
    match st with | Pulse_Syntax.Tm_IntroExists (uu___, t, uu___1) -> t
let (intro_exists_witness_singleton : Pulse_Syntax.st_term -> Prims.bool) =
  fun st ->
    match st with
    | Pulse_Syntax.Tm_IntroExists (uu___, uu___1, uu___2::[]) -> true
    | uu___ -> false
let (check_intro_exists_erased :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        unit FStar_Pervasives_Native.option ->
          Pulse_Syntax.term ->
            unit ->
              Pulse_Syntax.term FStar_Pervasives_Native.option ->
                ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                   (unit, unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun st ->
        fun vprop_typing ->
          fun pre ->
            fun pre_typing ->
              fun post_hint ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (403)) (Prims.of_int (31))
                     (Prims.of_int (403)) (Prims.of_int (33)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (403)) (Prims.of_int (2))
                     (Prims.of_int (421)) (Prims.of_int (56)))
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> st))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | Pulse_Syntax.Tm_IntroExists (uu___1, t, e::[]) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (405)) (Prims.of_int (4))
                                    (Prims.of_int (407)) (Prims.of_int (28)))
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (404)) (Prims.of_int (2))
                                    (Prims.of_int (421)) (Prims.of_int (56)))
                                 (match vprop_typing with
                                  | FStar_Pervasives_Native.Some typing ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 Prims.Mkdtuple2 (t, ()))))
                                  | uu___2 ->
                                      Obj.magic
                                        (Obj.repr
                                           (Pulse_Checker_Pure.check_vprop f
                                              g t)))
                                 (fun uu___2 ->
                                    (fun uu___2 ->
                                       match uu___2 with
                                       | Prims.Mkdtuple2 (t1, t_typing) ->
                                           (match t1 with
                                            | Pulse_Syntax.Tm_ExistsSL
                                                (u, ty, p, uu___3) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (412))
                                                           (Prims.of_int (30))
                                                           (Prims.of_int (412))
                                                           (Prims.of_int (51)))
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (412))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (420))
                                                           (Prims.of_int (58)))
                                                        (Obj.magic
                                                           (Pulse_Checker_Pure.check_universe
                                                              f g ty))
                                                        (fun uu___4 ->
                                                           (fun uu___4 ->
                                                              match uu___4
                                                              with
                                                              | Prims.Mkdtuple2
                                                                  (u',
                                                                   ty_typing)
                                                                  ->
                                                                  if u = u'
                                                                  then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_tot_with_expected_typ
                                                                    f g e
                                                                    (Pulse_Typing.mk_erased
                                                                    u ty)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (e1,
                                                                    e_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_IntroExistsErased
                                                                    (g, u,
                                                                    ty, p,
                                                                    e1, (),
                                                                    (), ())))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (56)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    f g
                                                                    (Pulse_Syntax.Tm_IntroExists
                                                                    (true,
                                                                    (Pulse_Syntax.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax.should_elim_false)),
                                                                    [e1]))
                                                                    pre ()
                                                                    (Pulse_Typing.comp_intro_exists_erased
                                                                    u ty p e1)
                                                                    d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (repack f
                                                                    g pre
                                                                    (Pulse_Syntax.Tm_IntroExists
                                                                    (true,
                                                                    (Pulse_Syntax.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax.should_elim_false)),
                                                                    [e1]))
                                                                    uu___6
                                                                    post_hint
                                                                    true))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                  else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Universe checking failed in intro_exists")))
                                                             uu___4)))
                                            | uu___3 ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Derived.fail
                                                        "elim_exists argument not a Tm_ExistsSL"))))
                                      uu___2))) uu___)
let (check_intro_exists :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        unit FStar_Pervasives_Native.option ->
          Pulse_Syntax.term ->
            unit ->
              Pulse_Syntax.term FStar_Pervasives_Native.option ->
                ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                   (unit, unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun st ->
        fun vprop_typing ->
          fun pre ->
            fun pre_typing ->
              fun post_hint ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (436)) (Prims.of_int (31))
                     (Prims.of_int (436)) (Prims.of_int (33)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (436)) (Prims.of_int (2))
                     (Prims.of_int (454)) (Prims.of_int (56)))
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> st))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | Pulse_Syntax.Tm_IntroExists (uu___1, t, e::[]) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (438)) (Prims.of_int (4))
                                    (Prims.of_int (440)) (Prims.of_int (28)))
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (437)) (Prims.of_int (2))
                                    (Prims.of_int (454)) (Prims.of_int (56)))
                                 (match vprop_typing with
                                  | FStar_Pervasives_Native.Some typing ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 Prims.Mkdtuple2 (t, ()))))
                                  | uu___2 ->
                                      Obj.magic
                                        (Obj.repr
                                           (Pulse_Checker_Pure.check_vprop f
                                              g t)))
                                 (fun uu___2 ->
                                    (fun uu___2 ->
                                       match uu___2 with
                                       | Prims.Mkdtuple2 (t1, t_typing) ->
                                           (match t1 with
                                            | Pulse_Syntax.Tm_ExistsSL
                                                (u, ty, p, uu___3) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (445))
                                                           (Prims.of_int (30))
                                                           (Prims.of_int (445))
                                                           (Prims.of_int (51)))
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (445))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (453))
                                                           (Prims.of_int (58)))
                                                        (Obj.magic
                                                           (Pulse_Checker_Pure.check_universe
                                                              f g ty))
                                                        (fun uu___4 ->
                                                           (fun uu___4 ->
                                                              match uu___4
                                                              with
                                                              | Prims.Mkdtuple2
                                                                  (u',
                                                                   ty_typing)
                                                                  ->
                                                                  if u = u'
                                                                  then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_tot_with_expected_typ
                                                                    f g e ty))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (e1,
                                                                    e_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (70)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_IntroExists
                                                                    (g, u,
                                                                    ty, p,
                                                                    e1, (),
                                                                    (), ())))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (56)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    f g
                                                                    (Pulse_Syntax.Tm_IntroExists
                                                                    (false,
                                                                    (Pulse_Syntax.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax.should_elim_false)),
                                                                    [e1]))
                                                                    pre ()
                                                                    (Pulse_Typing.comp_intro_exists
                                                                    u ty p e1)
                                                                    d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (repack f
                                                                    g pre
                                                                    (Pulse_Syntax.Tm_IntroExists
                                                                    (false,
                                                                    (Pulse_Syntax.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax.should_elim_false)),
                                                                    [e1]))
                                                                    uu___6
                                                                    post_hint
                                                                    true))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                  else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Universe checking failed in intro_exists")))
                                                             uu___4)))
                                            | uu___3 ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Derived.fail
                                                        "elim_exists argument not a Tm_ExistsSL"))))
                                      uu___2))) uu___)
let (check_intro_exists_either :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        unit FStar_Pervasives_Native.option ->
          Pulse_Syntax.term ->
            unit ->
              Pulse_Syntax.term FStar_Pervasives_Native.option ->
                ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                   (unit, unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun st ->
        fun vprop_typing ->
          fun pre ->
            fun pre_typing ->
              fun post_hint ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (467)) (Prims.of_int (4))
                     (Prims.of_int (468)) (Prims.of_int (71)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (469)) (Prims.of_int (4))
                     (Prims.of_int (471)) (Prims.of_int (72)))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (467)) (Prims.of_int (12))
                           (Prims.of_int (468)) (Prims.of_int (71)))
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (467)) (Prims.of_int (4))
                           (Prims.of_int (468)) (Prims.of_int (71)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "Pulse.Checker.fst"
                                 (Prims.of_int (468)) (Prims.of_int (28))
                                 (Prims.of_int (468)) (Prims.of_int (70)))
                              (FStar_Range.mk_range "prims.fst"
                                 (Prims.of_int (590)) (Prims.of_int (19))
                                 (Prims.of_int (590)) (Prims.of_int (31)))
                              (Obj.magic
                                 (Pulse_Syntax_Printer.term_to_string
                                    (intro_exists_vprop st)))
                              (fun uu___ ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      Prims.strcat "LOG INTRO EXISTS: "
                                        (Prims.strcat uu___ "")))))
                        (fun uu___ ->
                           (fun uu___ ->
                              Obj.magic (FStar_Tactics_Builtins.print uu___))
                             uu___)))
                  (fun uu___ ->
                     (fun uu___ ->
                        if is_intro_exists_erased st
                        then
                          Obj.magic
                            (check_intro_exists_erased f g st vprop_typing
                               pre () post_hint)
                        else
                          Obj.magic
                            (check_intro_exists f g st vprop_typing pre ()
                               post_hint)) uu___)
let rec (prepare_instantiations :
  (Pulse_Syntax.vprop * (Pulse_Syntax.term, Pulse_Syntax.term)
    FStar_Pervasives.either) Prims.list ->
    Pulse_Syntax.term ->
      Pulse_Syntax.term Prims.list ->
        ((Pulse_Syntax.vprop * (Pulse_Syntax.vprop * (Pulse_Syntax.term,
           Pulse_Syntax.term) FStar_Pervasives.either) Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun out ->
           fun goal_vprop ->
             fun witnesses ->
               match (witnesses, goal_vprop) with
               | ([], Pulse_Syntax.Tm_ExistsSL (u, ty, p, uu___)) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (478)) (Prims.of_int (10))
                              (Prims.of_int (479)) (Prims.of_int (33)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (477)) (Prims.of_int (6))
                              (Prims.of_int (481)) (Prims.of_int (73)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (478)) (Prims.of_int (18))
                                    (Prims.of_int (478)) (Prims.of_int (29)))
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (479)) (Prims.of_int (10))
                                    (Prims.of_int (479)) (Prims.of_int (33)))
                                 (Obj.magic (Pulse_Syntax.gen_uvar ty))
                                 (fun t ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 ->
                                         ((Pulse_Syntax.open_term' p t
                                             Prims.int_zero),
                                           (FStar_Pervasives.Inr t))))))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 match uu___1 with
                                 | (next_goal_vprop, inst) ->
                                     Obj.magic
                                       (prepare_instantiations
                                          ((goal_vprop, inst) :: out)
                                          next_goal_vprop [])) uu___1)))
               | ([], uu___) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> (goal_vprop, out))))
               | (t::witnesses1, Pulse_Syntax.Tm_ExistsSL (u, ty, p, uu___))
                   ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (488)) (Prims.of_int (10))
                              (Prims.of_int (493)) (Prims.of_int (35)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (487)) (Prims.of_int (6))
                              (Prims.of_int (495)) (Prims.of_int (80)))
                           (match t with
                            | Pulse_Syntax.Tm_Unknown ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (490))
                                           (Prims.of_int (20))
                                           (Prims.of_int (490))
                                           (Prims.of_int (31)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (491))
                                           (Prims.of_int (12))
                                           (Prims.of_int (491))
                                           (Prims.of_int (35)))
                                        (Obj.magic (Pulse_Syntax.gen_uvar ty))
                                        (fun t1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                ((Pulse_Syntax.open_term' p
                                                    t1 Prims.int_zero),
                                                  (FStar_Pervasives.Inr t1))))))
                            | uu___1 ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           ((Pulse_Syntax.open_term' p t
                                               Prims.int_zero),
                                             (FStar_Pervasives.Inl t))))))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 match uu___1 with
                                 | (next_goal_vprop, inst) ->
                                     Obj.magic
                                       (prepare_instantiations
                                          ((goal_vprop, inst) :: out)
                                          next_goal_vprop witnesses1)) uu___1)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Derived.fail
                           "Unexpected number of instantiations in intro")))
          uu___2 uu___1 uu___
let (maybe_infer_intro_exists :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        Pulse_Syntax.term ->
          (Pulse_Syntax.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun st ->
        fun pre ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (507))
               (Prims.of_int (8)) (Prims.of_int (518)) (Prims.of_int (18)))
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (520))
               (Prims.of_int (4)) (Prims.of_int (625)) (Prims.of_int (40)))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  fun t ->
                    match FStar_List_Tot_Base.partition
                            (fun uu___1 ->
                               match uu___1 with
                               | Pulse_Syntax.Tm_Pure uu___2 -> false
                               | Pulse_Syntax.Tm_Emp -> false
                               | uu___2 -> true)
                            (Pulse_Checker_Framing.vprop_as_list t)
                    with
                    | (rest, pure) ->
                        (((match Pulse_Checker_Framing.list_as_vprop rest
                           with
                           | Pulse_Syntax.Tm_Star (t1, Pulse_Syntax.Tm_Emp)
                               -> t1
                           | Pulse_Syntax.Tm_Star (Pulse_Syntax.Tm_Emp, t1)
                               -> t1
                           | t1 -> t1)), pure)))
            (fun uu___ ->
               (fun remove_pure_conjuncts ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Checker.fst"
                          (Prims.of_int (521)) (Prims.of_int (6))
                          (Prims.of_int (537)) (Prims.of_int (17)))
                       (FStar_Range.mk_range "Pulse.Checker.fst"
                          (Prims.of_int (558)) (Prims.of_int (4))
                          (Prims.of_int (625)) (Prims.of_int (40)))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             fun t ->
                               match t with
                               | Pulse_Syntax.Tm_PureApp
                                   (Pulse_Syntax.Tm_PureApp
                                    (Pulse_Syntax.Tm_PureApp
                                     (hd, FStar_Pervasives_Native.Some
                                      (Pulse_Syntax.Implicit), uu___1),
                                     FStar_Pervasives_Native.None, l),
                                    FStar_Pervasives_Native.None, r)
                                   ->
                                   (match hd with
                                    | Pulse_Syntax.Tm_FVar fv ->
                                        if
                                          fv =
                                            (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                               "eq2_prop")
                                        then
                                          FStar_Pervasives_Native.Some (l, r)
                                        else FStar_Pervasives_Native.None
                                    | Pulse_Syntax.Tm_UInst (fv, uu___2) ->
                                        if
                                          fv =
                                            (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                               "eq2_prop")
                                        then
                                          FStar_Pervasives_Native.Some (l, r)
                                        else FStar_Pervasives_Native.None
                                    | uu___2 -> FStar_Pervasives_Native.None)
                               | uu___1 -> FStar_Pervasives_Native.None))
                       (fun uu___ ->
                          (fun is_eq2 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range "Pulse.Checker.fst"
                                     (Prims.of_int (558)) (Prims.of_int (44))
                                     (Prims.of_int (558)) (Prims.of_int (46)))
                                  (FStar_Range.mk_range "Pulse.Checker.fst"
                                     (Prims.of_int (558)) (Prims.of_int (4))
                                     (Prims.of_int (625)) (Prims.of_int (40)))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ -> st))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        match uu___ with
                                        | Pulse_Syntax.Tm_IntroExists
                                            (erased, t, witnesses) ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.fst"
                                                    (Prims.of_int (559))
                                                    (Prims.of_int (28))
                                                    (Prims.of_int (559))
                                                    (Prims.of_int (45)))
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.fst"
                                                    (Prims.of_int (559))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (625))
                                                    (Prims.of_int (40)))
                                                 (Obj.magic
                                                    (Pulse_Checker_Pure.check_vprop
                                                       f g t))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       match uu___1 with
                                                       | Prims.Mkdtuple2
                                                           (t1, t_typing) ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.fst"
                                                                   (Prims.of_int (560))
                                                                   (Prims.of_int (28))
                                                                   (Prims.of_int (560))
                                                                   (Prims.of_int (65)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.fst"
                                                                   (Prims.of_int (560))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (625))
                                                                   (Prims.of_int (40)))
                                                                (Obj.magic
                                                                   (prepare_instantiations
                                                                    [] t1
                                                                    witnesses))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (goal_vprop,
                                                                    insts) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    remove_pure_conjuncts
                                                                    goal_vprop))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (goal_vprop1,
                                                                    pure_conjuncts)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (79)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (563))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (40)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.try_inst_uvs_in_goal
                                                                    pre
                                                                    goal_vprop1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    solutions
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (564))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (577))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun
                                                                    solutions1
                                                                    ->
                                                                    fun p ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (564))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (564))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (565))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (577))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    p))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun p1
                                                                    ->
                                                                    match p1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax.Tm_Pure
                                                                    p2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    is_eq2 p2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (l, r) ->
                                                                    Obj.repr
                                                                    (if
                                                                    (Pulse_Checker_Inference.contains_uvar
                                                                    l) ||
                                                                    (Pulse_Checker_Inference.contains_uvar
                                                                    r)
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.try_unify
                                                                    l r))
                                                                    (fun sols
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    sols
                                                                    solutions1)))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    solutions1)))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    solutions1))))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    solutions1))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    maybe_solve_pure
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (580))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (40)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.fold_left
                                                                    maybe_solve_pure
                                                                    solutions
                                                                    pure_conjuncts))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    solutions1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (581))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (587))
                                                                    (Prims.of_int (19)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun t2 ->
                                                                    match t2
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax.Tm_PureApp
                                                                    (Pulse_Syntax.Tm_PureApp
                                                                    (Pulse_Syntax.Tm_UInst
                                                                    (l,
                                                                    uu___5::[]),
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.Implicit),
                                                                    uu___6),
                                                                    FStar_Pervasives_Native.None,
                                                                    arg) ->
                                                                    if
                                                                    l =
                                                                    Pulse_Reflection_Util.reveal_lid
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    arg
                                                                    else
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    un_reveal
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (591))
                                                                    (Prims.of_int (28)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun e ->
                                                                    Pulse_Syntax.Tm_PureApp
                                                                    ((Pulse_Syntax.Tm_FVar
                                                                    Pulse_Reflection_Util.hide_lid),
                                                                    FStar_Pervasives_Native.None,
                                                                    e)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    mk_hide
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (17)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (u, v) ->
                                                                    (match 
                                                                    un_reveal
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___6 ->
                                                                    (u,
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v))
                                                                    | 
                                                                    uu___6 ->
                                                                    (u,
                                                                    (mk_hide
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v)))))
                                                                    solutions1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    solutions2
                                                                    ->
                                                                    let rec build_instantiations
                                                                    solutions3
                                                                    insts1 =
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (605))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (v, i) ->
                                                                    (match i
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    user_provided
                                                                    ->
                                                                    Pulse_Syntax.Tm_IntroExists
                                                                    (false,
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    v),
                                                                    [user_provided])
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    inferred
                                                                    ->
                                                                    (match 
                                                                    un_reveal
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    inferred)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    sol ->
                                                                    Pulse_Syntax.Tm_IntroExists
                                                                    (true,
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    v),
                                                                    [sol])
                                                                    | 
                                                                    uu___6 ->
                                                                    Pulse_Syntax.Tm_IntroExists
                                                                    (true,
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    v),
                                                                    [
                                                                    Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    inferred])))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    one_inst
                                                                    ->
                                                                    match insts1
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Impossible"))
                                                                    | 
                                                                    hd::[] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax.Tm_Protect
                                                                    (one_inst
                                                                    hd))))
                                                                    | 
                                                                    hd::tl ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (build_instantiations
                                                                    solutions3
                                                                    tl))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax.Tm_Bind
                                                                    ((Pulse_Syntax.Tm_Protect
                                                                    (one_inst
                                                                    hd)),
                                                                    uu___4)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax.Tm_Protect
                                                                    uu___4)))))
                                                                    uu___4) in
                                                                    Obj.magic
                                                                    (build_instantiations
                                                                    solutions2
                                                                    insts))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                      uu___1))) uu___)))
                            uu___))) uu___)
let (check_while :
  Prims.bool ->
    FStar_Reflection_Typing.fstar_top_env ->
      Pulse_Typing.env ->
        Pulse_Syntax.st_term ->
          Pulse_Syntax.term ->
            unit ->
              Pulse_Syntax.term FStar_Pervasives_Native.option ->
                (Prims.bool -> Pulse_Checker_Common.check_t) ->
                  ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                     (unit, unit, unit, unit) Pulse_Typing.st_typing)
                     FStar_Pervasives.dtuple3,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun f ->
      fun g ->
        fun t ->
          fun pre ->
            fun pre_typing ->
              fun post_hint ->
                fun check' ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (674)) (Prims.of_int (31))
                       (Prims.of_int (674)) (Prims.of_int (32)))
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (674)) (Prims.of_int (2))
                       (Prims.of_int (704)) (Prims.of_int (56)))
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t))
                    (fun uu___ ->
                       (fun uu___ ->
                          match uu___ with
                          | Pulse_Syntax.Tm_While (inv, cond, body) ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (676)) (Prims.of_int (4))
                                      (Prims.of_int (676))
                                      (Prims.of_int (69)))
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (675)) (Prims.of_int (2))
                                      (Prims.of_int (704))
                                      (Prims.of_int (56)))
                                   (Obj.magic
                                      (Pulse_Checker_Pure.check_vprop f g
                                         (Pulse_Syntax.Tm_ExistsSL
                                            (Pulse_Syntax.U_zero,
                                              Pulse_Typing.tm_bool, inv,
                                              Pulse_Syntax.should_elim_true))))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         match uu___1 with
                                         | Prims.Mkdtuple2 (inv1, inv_typing)
                                             ->
                                             (match inv1 with
                                              | Pulse_Syntax.Tm_ExistsSL
                                                  (Pulse_Syntax.U_zero,
                                                   Pulse_Syntax.Tm_FVar
                                                   ("Prims"::"bool"::[]),
                                                   inv2, uu___2)
                                                  ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.fst"
                                                             (Prims.of_int (681))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (681))
                                                             (Prims.of_int (64)))
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.fst"
                                                             (Prims.of_int (682))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (703))
                                                             (Prims.of_int (55)))
                                                          (Obj.magic
                                                             (Pulse_Checker_Pure.check_vprop_with_core
                                                                f g
                                                                (Pulse_Syntax.comp_pre
                                                                   (Pulse_Typing.comp_while_cond
                                                                    inv2))))
                                                          (fun uu___3 ->
                                                             (fun
                                                                cond_pre_typing
                                                                ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (682))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (703))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (64)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.print
                                                                    "Check: While condition"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    f g cond
                                                                    (Pulse_Syntax.comp_pre
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv2)) ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.comp_post
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv2)))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (cond1,
                                                                    cond_comp,
                                                                    cond_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax.eq_comp
                                                                    cond_comp
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv2)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (701))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    f g
                                                                    (Pulse_Syntax.comp_pre
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv2))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body_pre_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (701))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (66)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.print
                                                                    "Check: While body"))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    f g body
                                                                    (Pulse_Syntax.comp_pre
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv2)) ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.comp_post
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv2)))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    body_comp,
                                                                    body_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax.eq_comp
                                                                    body_comp
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv2)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (79)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_While
                                                                    (g, inv2,
                                                                    cond1,
                                                                    body1,
                                                                    (),
                                                                    cond_typing,
                                                                    body_typing)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (47)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (47)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    pre))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (47)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (70)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax.comp_pre
                                                                    (Pulse_Typing.comp_while
                                                                    inv2))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Check: Framing while\ninferred pre="
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    "\n required pre="))
                                                                    (Prims.strcat
                                                                    x "\n")))))
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
                                                                    (FStar_Tactics_Builtins.print
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    f g
                                                                    (Pulse_Syntax.Tm_While
                                                                    (inv2,
                                                                    cond1,
                                                                    body1))
                                                                    pre ()
                                                                    (Pulse_Typing.comp_while
                                                                    inv2) d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (repack f
                                                                    g pre
                                                                    (Pulse_Syntax.Tm_While
                                                                    (inv2,
                                                                    cond1,
                                                                    body1))
                                                                    uu___6
                                                                    post_hint
                                                                    true))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Cannot typecheck while loop body")))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Cannot typecheck while loop condition")))
                                                                    uu___3)))
                                                               uu___3)))
                                              | uu___2 ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Derived.fail
                                                          "Typechecked invariant is not an exists"))))
                                        uu___1))) uu___)
let (maybe_log :
  Pulse_Syntax.st_term -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun t ->
       match t with
       | Pulse_Syntax.Tm_STApp
           (Pulse_Syntax.Tm_FVar l, FStar_Pervasives_Native.None, p) ->
           Obj.magic
             (Obj.repr
                (if l = elim_pure_explicit_lid
                 then
                   Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (710)) (Prims.of_int (17))
                           (Prims.of_int (711)) (Prims.of_int (41)))
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (710)) (Prims.of_int (9))
                           (Prims.of_int (711)) (Prims.of_int (41)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "Pulse.Checker.fst"
                                 (Prims.of_int (711)) (Prims.of_int (20))
                                 (Prims.of_int (711)) (Prims.of_int (40)))
                              (FStar_Range.mk_range "prims.fst"
                                 (Prims.of_int (590)) (Prims.of_int (19))
                                 (Prims.of_int (590)) (Prims.of_int (31)))
                              (Obj.magic
                                 (Pulse_Syntax_Printer.term_to_string p))
                              (fun uu___ ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      Prims.strcat "LOG ELIM PURE: "
                                        (Prims.strcat uu___ "\n")))))
                        (fun uu___ ->
                           (fun uu___ ->
                              Obj.magic (FStar_Tactics_Builtins.print uu___))
                             uu___))
                 else
                   Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
       | Pulse_Syntax.Tm_STApp
           (Pulse_Syntax.Tm_PureApp
            (Pulse_Syntax.Tm_FVar l, FStar_Pervasives_Native.None, p),
            FStar_Pervasives_Native.None, uu___)
           ->
           Obj.magic
             (Obj.repr
                (if
                   l =
                     (Pulse_Reflection_Util.mk_steel_wrapper_lid "intro_pure")
                 then
                   Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (715)) (Prims.of_int (17))
                           (Prims.of_int (716)) (Prims.of_int (41)))
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (715)) (Prims.of_int (9))
                           (Prims.of_int (716)) (Prims.of_int (41)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "Pulse.Checker.fst"
                                 (Prims.of_int (716)) (Prims.of_int (20))
                                 (Prims.of_int (716)) (Prims.of_int (40)))
                              (FStar_Range.mk_range "prims.fst"
                                 (Prims.of_int (590)) (Prims.of_int (19))
                                 (Prims.of_int (590)) (Prims.of_int (31)))
                              (Obj.magic
                                 (Pulse_Syntax_Printer.term_to_string p))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      Prims.strcat "LOG INTRO PURE: "
                                        (Prims.strcat uu___1 "\n")))))
                        (fun uu___1 ->
                           (fun uu___1 ->
                              Obj.magic (FStar_Tactics_Builtins.print uu___1))
                             uu___1))
                 else
                   Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
       | uu___ ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
      uu___
let (check_stapp :
  Prims.bool ->
    FStar_Reflection_Typing.fstar_top_env ->
      Pulse_Typing.env ->
        Pulse_Syntax.st_term ->
          Pulse_Syntax.term ->
            unit ->
              Pulse_Syntax.term FStar_Pervasives_Native.option ->
                (Prims.bool -> Pulse_Checker_Common.check_t) ->
                  ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                     (unit, unit, unit, unit) Pulse_Typing.st_typing)
                     FStar_Pervasives.dtuple3,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun f ->
      fun g ->
        fun t ->
          fun pre ->
            fun pre_typing ->
              fun post_hint ->
                fun check' ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (732)) (Prims.of_int (2))
                       (Prims.of_int (732)) (Prims.of_int (13)))
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (733)) (Prims.of_int (2))
                       (Prims.of_int (781)) (Prims.of_int (112)))
                    (Obj.magic (maybe_log t))
                    (fun uu___ ->
                       (fun uu___ ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (733)) (Prims.of_int (31))
                                  (Prims.of_int (733)) (Prims.of_int (32)))
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (733)) (Prims.of_int (2))
                                  (Prims.of_int (781)) (Prims.of_int (112)))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 -> t))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | Pulse_Syntax.Tm_STApp
                                         (head, qual, arg) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (742))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (755))
                                                 (Prims.of_int (34)))
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (757))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (781))
                                                 (Prims.of_int (112)))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    fun t1 ->
                                                      fun c ->
                                                        match c with
                                                        | Pulse_Syntax.C_Tot
                                                            (Pulse_Syntax.Tm_Arrow
                                                            (uu___3,
                                                             FStar_Pervasives_Native.Some
                                                             implicit,
                                                             uu___4))
                                                            ->
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (744))
                                                                 (Prims.of_int (21))
                                                                 (Prims.of_int (744))
                                                                 (Prims.of_int (22)))
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (744))
                                                                 (Prims.of_int (6))
                                                                 (Prims.of_int (747))
                                                                 (Prims.of_int (49)))
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___5
                                                                    -> c))
                                                              (fun uu___5 ->
                                                                 (fun uu___5
                                                                    ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax.C_Tot
                                                                    ty ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (49)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.infer
                                                                    t1 ty pre))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (check'
                                                                    false f g
                                                                    t2 pre ()
                                                                    post_hint))
                                                                    uu___6)))
                                                                   uu___5)
                                                        | uu___3 ->
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (751))
                                                                 (Prims.of_int (8))
                                                                 (Prims.of_int (755))
                                                                 (Prims.of_int (34)))
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (750))
                                                                 (Prims.of_int (6))
                                                                 (Prims.of_int (755))
                                                                 (Prims.of_int (34)))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (755))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (755))
                                                                    (Prims.of_int (33)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (751))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (755))
                                                                    (Prims.of_int (34)))
                                                                    (
                                                                    Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    arg))
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (751))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (755))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (751))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (755))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (754))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (754))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (751))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (755))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (751))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (755))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (751))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (755))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (753))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (753))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Unexpected c in infer_logical_implicits_and_check (head: "
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    ", comp_typ: "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", and arg: "))
                                                                    (Prims.strcat
                                                                    x1 ")")))))
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
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    uu___4))))
                                                                    uu___4)))
                                                              (fun uu___4 ->
                                                                 FStar_Tactics_Derived.fail
                                                                   uu___4)))
                                              (fun uu___2 ->
                                                 (fun
                                                    infer_logical_implicits_and_check
                                                    ->
                                                    Obj.magic
                                                      (FStar_Tactics_Derived.or_else
                                                         (fun uu___2 ->
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (758))
                                                                 (Prims.of_int (29))
                                                                 (Prims.of_int (758))
                                                                 (Prims.of_int (53)))
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (759))
                                                                 (Prims.of_int (11))
                                                                 (Prims.of_int (760))
                                                                 (Prims.of_int (57)))
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___3
                                                                    ->
                                                                    Pulse_Syntax.Tm_PureApp
                                                                    (head,
                                                                    qual,
                                                                    arg)))
                                                              (fun uu___3 ->
                                                                 (fun
                                                                    pure_app
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (759))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (759))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (759))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (760))
                                                                    (Prims.of_int (57)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.instantiate_implicits
                                                                    f g
                                                                    pure_app))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (t1, ty)
                                                                    ->
                                                                    Obj.magic
                                                                    (infer_logical_implicits_and_check
                                                                    t1
                                                                    (Pulse_Syntax.C_Tot
                                                                    ty)))
                                                                    uu___3)))
                                                                   uu___3))
                                                         (fun uu___2 ->
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (762))
                                                                 (Prims.of_int (38))
                                                                 (Prims.of_int (762))
                                                                 (Prims.of_int (56)))
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (762))
                                                                 (Prims.of_int (5))
                                                                 (Prims.of_int (781))
                                                                 (Prims.of_int (111)))
                                                              (Obj.magic
                                                                 (Pulse_Checker_Pure.check_tot
                                                                    f g head))
                                                              (fun uu___3 ->
                                                                 (fun uu___3
                                                                    ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (head1,
                                                                    ty_head,
                                                                    dhead) ->
                                                                    (match ty_head
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax.Tm_Arrow
                                                                    ({
                                                                    Pulse_Syntax.binder_ty
                                                                    = formal;
                                                                    Pulse_Syntax.binder_ppname
                                                                    = ppname;_},
                                                                    bqual,
                                                                    comp_typ)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    qual =
                                                                    bqual
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (767))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (767))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (767))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (778))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_tot_with_expected_typ
                                                                    f g arg
                                                                    formal))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (arg1,
                                                                    darg) ->
                                                                    (match comp_typ
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax.C_ST
                                                                    res ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (773))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (773))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    f g
                                                                    (Pulse_Syntax.Tm_STApp
                                                                    (head1,
                                                                    qual,
                                                                    arg1))
                                                                    pre ()
                                                                    (Pulse_Syntax.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (repack f
                                                                    g pre
                                                                    (Pulse_Syntax.Tm_STApp
                                                                    (head1,
                                                                    qual,
                                                                    arg1))
                                                                    uu___5
                                                                    post_hint
                                                                    true))
                                                                    uu___5)))
                                                                    uu___5))
                                                                    | 
                                                                    Pulse_Syntax.C_STAtomic
                                                                    (uu___5,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (773))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (773))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    f g
                                                                    (Pulse_Syntax.Tm_STApp
                                                                    (head1,
                                                                    qual,
                                                                    arg1))
                                                                    pre ()
                                                                    (Pulse_Syntax.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (repack f
                                                                    g pre
                                                                    (Pulse_Syntax.Tm_STApp
                                                                    (head1,
                                                                    qual,
                                                                    arg1))
                                                                    uu___6
                                                                    post_hint
                                                                    true))
                                                                    uu___6)))
                                                                    uu___6))
                                                                    | 
                                                                    Pulse_Syntax.C_STGhost
                                                                    (uu___5,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (773))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (773))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (774))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    f g
                                                                    (Pulse_Syntax.Tm_STApp
                                                                    (head1,
                                                                    qual,
                                                                    arg1))
                                                                    pre ()
                                                                    (Pulse_Syntax.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (repack f
                                                                    g pre
                                                                    (Pulse_Syntax.Tm_STApp
                                                                    (head1,
                                                                    qual,
                                                                    arg1))
                                                                    uu___6
                                                                    post_hint
                                                                    true))
                                                                    uu___6)))
                                                                    uu___6))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (776))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (776))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (777))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (778))
                                                                    (Prims.of_int (55)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax.Tm_PureApp
                                                                    (head1,
                                                                    qual,
                                                                    arg1)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (777))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (777))
                                                                    (Prims.of_int (53)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (778))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (778))
                                                                    (Prims.of_int (55)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax.open_comp_with
                                                                    comp_typ
                                                                    arg1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    comp_typ1
                                                                    ->
                                                                    Obj.magic
                                                                    (infer_logical_implicits_and_check
                                                                    t1
                                                                    comp_typ1))
                                                                    uu___6)))
                                                                    uu___6))))
                                                                    uu___4))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Unexpected qualifier")))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (781))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (781))
                                                                    (Prims.of_int (111)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (781))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (781))
                                                                    (Prims.of_int (111)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (781))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (781))
                                                                    (Prims.of_int (110)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty_head))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Unexpected head type in impure application: "
                                                                    (Prims.strcat
                                                                    uu___5 "")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___5)))))
                                                                   uu___3))))
                                                   uu___2))) uu___1))) uu___)
let (check_admit :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        Pulse_Syntax.term ->
          unit ->
            Pulse_Syntax.term FStar_Pervasives_Native.option ->
              ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                 (unit, unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (794)) (Prims.of_int (28))
                   (Prims.of_int (794)) (Prims.of_int (29)))
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (794)) (Prims.of_int (2))
                   (Prims.of_int (816)) (Prims.of_int (4)))
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax.Tm_Admit (c, uu___1, t1, post) ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (795)) (Prims.of_int (26))
                                  (Prims.of_int (795)) (Prims.of_int (46)))
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (795)) (Prims.of_int (2))
                                  (Prims.of_int (816)) (Prims.of_int (4)))
                               (Obj.magic
                                  (Pulse_Checker_Pure.check_universe f g t1))
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     match uu___2 with
                                     | Prims.Mkdtuple2 (u, t_typing) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (796))
                                                 (Prims.of_int (10))
                                                 (Prims.of_int (796))
                                                 (Prims.of_int (17)))
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (797))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (816))
                                                 (Prims.of_int (4)))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    Pulse_Typing.fresh g))
                                              (fun uu___3 ->
                                                 (fun x ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (798))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (803))
                                                            (Prims.of_int (26)))
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (805))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (816))
                                                            (Prims.of_int (4)))
                                                         (match (post,
                                                                  post_hint)
                                                          with
                                                          | (FStar_Pervasives_Native.None,
                                                             FStar_Pervasives_Native.None)
                                                              ->
                                                              FStar_Tactics_Derived.fail
                                                                "T_Admit: either no post or two posts"
                                                          | (FStar_Pervasives_Native.Some
                                                             uu___3,
                                                             FStar_Pervasives_Native.Some
                                                             uu___4) ->
                                                              FStar_Tactics_Derived.fail
                                                                "T_Admit: either no post or two posts"
                                                          | (FStar_Pervasives_Native.Some
                                                             post1, uu___3)
                                                              ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   -> post1)
                                                          | (uu___3,
                                                             FStar_Pervasives_Native.Some
                                                             post1) ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   -> post1))
                                                         (fun uu___3 ->
                                                            (fun post1 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (805))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (805))
                                                                    (Prims.of_int (36)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (806))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (4)))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax.open_term
                                                                    post1 x))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    post_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (807))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (807))
                                                                    (Prims.of_int (70)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (806))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (4)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_tot_with_expected_typ
                                                                    f
                                                                    ((x,
                                                                    (FStar_Pervasives.Inl
                                                                    t1)) ::
                                                                    g)
                                                                    post_opened
                                                                    Pulse_Syntax.Tm_VProp))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened1,
                                                                    post_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax.Tm_Admit
                                                                    (c, u,
                                                                    t1,
                                                                    FStar_Pervasives_Native.None)),
                                                                    (Pulse_Typing.comp_admit
                                                                    c
                                                                    {
                                                                    Pulse_Syntax.u
                                                                    = u;
                                                                    Pulse_Syntax.res
                                                                    = t1;
                                                                    Pulse_Syntax.pre
                                                                    = pre;
                                                                    Pulse_Syntax.post
                                                                    =
                                                                    (Pulse_Syntax.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }),
                                                                    (Pulse_Typing.T_Admit
                                                                    (g,
                                                                    {
                                                                    Pulse_Syntax.u
                                                                    = u;
                                                                    Pulse_Syntax.res
                                                                    = t1;
                                                                    Pulse_Syntax.pre
                                                                    = pre;
                                                                    Pulse_Syntax.post
                                                                    =
                                                                    (Pulse_Syntax.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }, c,
                                                                    (Pulse_Typing.STC
                                                                    (g,
                                                                    {
                                                                    Pulse_Syntax.u
                                                                    = u;
                                                                    Pulse_Syntax.res
                                                                    = t1;
                                                                    Pulse_Syntax.pre
                                                                    = pre;
                                                                    Pulse_Syntax.post
                                                                    =
                                                                    (Pulse_Syntax.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }, x, (),
                                                                    (), ())))))))))
                                                                    uu___3)))
                                                              uu___3)))
                                                   uu___3))) uu___2))) uu___)
let (check_return :
  Prims.bool ->
    FStar_Reflection_Typing.fstar_top_env ->
      Pulse_Typing.env ->
        Pulse_Syntax.st_term ->
          Pulse_Syntax.term ->
            unit ->
              Pulse_Syntax.term FStar_Pervasives_Native.option ->
                ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                   (unit, unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun f ->
      fun g ->
        fun t ->
          fun pre ->
            fun pre_typing ->
              fun post_hint ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (830)) (Prims.of_int (29))
                     (Prims.of_int (830)) (Prims.of_int (30)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (830)) (Prims.of_int (2))
                     (Prims.of_int (847)) (Prims.of_int (52)))
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | Pulse_Syntax.Tm_Return (c, use_eq, t1) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (831)) (Prims.of_int (31))
                                    (Prims.of_int (831)) (Prims.of_int (51)))
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (831)) (Prims.of_int (2))
                                    (Prims.of_int (847)) (Prims.of_int (52)))
                                 (Obj.magic
                                    (Pulse_Checker_Pure.check_tot_univ f g t1))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       match uu___1 with
                                       | FStar_Pervasives.Mkdtuple5
                                           (t2, u, ty, uty, d) ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.fst"
                                                   (Prims.of_int (832))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (832))
                                                   (Prims.of_int (17)))
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.fst"
                                                   (Prims.of_int (833))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (847))
                                                   (Prims.of_int (52)))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      Pulse_Typing.fresh g))
                                                (fun uu___2 ->
                                                   (fun x ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.fst"
                                                              (Prims.of_int (834))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (844))
                                                              (Prims.of_int (27)))
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.fst"
                                                              (Prims.of_int (833))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (847))
                                                              (Prims.of_int (52)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (835))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (837))
                                                                    (Prims.of_int (25)))
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (838))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (844))
                                                                    (Prims.of_int (27)))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Pulse_Syntax.Tm_Emp
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    post))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (838))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (838))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (844))
                                                                    (Prims.of_int (27)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax.open_term
                                                                    post x))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    post_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (844))
                                                                    (Prims.of_int (27)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_tot_with_expected_typ
                                                                    f
                                                                    ((x,
                                                                    (FStar_Pervasives.Inl
                                                                    ty)) ::
                                                                    g)
                                                                    post_opened
                                                                    Pulse_Syntax.Tm_VProp))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened1,
                                                                    post_typing)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax.close_term
                                                                    post_opened1
                                                                    x), ())))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                           (fun uu___2 ->
                                                              (fun uu___2 ->
                                                                 match uu___2
                                                                 with
                                                                 | Prims.Mkdtuple2
                                                                    (post,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (846))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (846))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Return
                                                                    (g, c,
                                                                    use_eq,
                                                                    u, ty,
                                                                    t2, post,
                                                                    x, (),
                                                                    (), ())))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    f g
                                                                    (Pulse_Syntax.Tm_Return
                                                                    (c,
                                                                    use_eq,
                                                                    t2)) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_return
                                                                    c use_eq
                                                                    u ty t2
                                                                    post x)
                                                                    d1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (repack f
                                                                    g pre
                                                                    (Pulse_Syntax.Tm_Return
                                                                    (c,
                                                                    use_eq,
                                                                    t2))
                                                                    uu___3
                                                                    post_hint
                                                                    true))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                uu___2)))
                                                     uu___2))) uu___1)))
                       uu___)
let (handle_framing_failure :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        Pulse_Syntax.term ->
          unit ->
            Pulse_Syntax.term FStar_Pervasives_Native.option ->
              Pulse_Checker_Framing.framing_failure ->
                Pulse_Checker_Common.check_t ->
                  ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                     (unit, unit, unit, unit) Pulse_Typing.st_typing)
                     FStar_Pervasives.dtuple3,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t0 ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun failure ->
                fun check ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (862)) (Prims.of_int (6))
                       (Prims.of_int (872)) (Prims.of_int (42)))
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (874)) (Prims.of_int (4))
                       (Prims.of_int (913)) (Prims.of_int (30)))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          fun p ->
                            fun t ->
                              Pulse_Syntax.Tm_Protect
                                (Pulse_Syntax.Tm_Bind
                                   ((Pulse_Syntax.Tm_Protect
                                       (Pulse_Syntax.Tm_STApp
                                          ((Pulse_Syntax.Tm_PureApp
                                              ((Pulse_Syntax.Tm_FVar
                                                  (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                                     "intro_pure")),
                                                FStar_Pervasives_Native.None,
                                                p)),
                                            FStar_Pervasives_Native.None,
                                            (Pulse_Syntax.Tm_Constant
                                               Pulse_Syntax.Unit)))), t))))
                    (fun uu___ ->
                       (fun add_intro_pure ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (874)) (Prims.of_int (4))
                                  (Prims.of_int (879)) (Prims.of_int (65)))
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (880)) (Prims.of_int (4))
                                  (Prims.of_int (913)) (Prims.of_int (30)))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (874))
                                        (Prims.of_int (12))
                                        (Prims.of_int (879))
                                        (Prims.of_int (65)))
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (874))
                                        (Prims.of_int (4))
                                        (Prims.of_int (879))
                                        (Prims.of_int (65)))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.fst"
                                              (Prims.of_int (879))
                                              (Prims.of_int (21))
                                              (Prims.of_int (879))
                                              (Prims.of_int (64)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.fst"
                                              (Prims.of_int (874))
                                              (Prims.of_int (12))
                                              (Prims.of_int (879))
                                              (Prims.of_int (65)))
                                           (Obj.magic
                                              (terms_to_string
                                                 failure.Pulse_Checker_Framing.remaining_context))
                                           (fun uu___ ->
                                              (fun uu___ ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.fst"
                                                         (Prims.of_int (874))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (879))
                                                         (Prims.of_int (65)))
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.fst"
                                                         (Prims.of_int (874))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (879))
                                                         (Prims.of_int (65)))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.fst"
                                                               (Prims.of_int (878))
                                                               (Prims.of_int (21))
                                                               (Prims.of_int (878))
                                                               (Prims.of_int (70)))
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.fst"
                                                               (Prims.of_int (874))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (879))
                                                               (Prims.of_int (65)))
                                                            (Obj.magic
                                                               (terms_to_string
                                                                  failure.Pulse_Checker_Framing.unmatched_preconditions))
                                                            (fun uu___1 ->
                                                               (fun uu___1 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (879))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (879))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    t0))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Handling framing failure in term:\n"
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    "\nwith unmatched_pre={\n"))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\n} and context={\n"))
                                                                    (Prims.strcat
                                                                    x1 "\n}")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                                 uu___1)))
                                                      (fun uu___1 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___2 ->
                                                              uu___1 uu___))))
                                                uu___)))
                                     (fun uu___ ->
                                        (fun uu___ ->
                                           Obj.magic
                                             (FStar_Tactics_Builtins.print
                                                uu___)) uu___)))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (881))
                                             (Prims.of_int (6))
                                             (Prims.of_int (881))
                                             (Prims.of_int (91)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (880))
                                             (Prims.of_int (4))
                                             (Prims.of_int (913))
                                             (Prims.of_int (30)))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                FStar_List_Tot_Base.partition
                                                  (fun uu___2 ->
                                                     match uu___2 with
                                                     | Pulse_Syntax.Tm_Pure
                                                         uu___3 -> true
                                                     | uu___3 -> false)
                                                  failure.Pulse_Checker_Framing.unmatched_preconditions))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | (pures, rest) ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (884))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (890))
                                                            (Prims.of_int (13)))
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (892))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (913))
                                                            (Prims.of_int (30)))
                                                         (Obj.magic
                                                            (FStar_Tactics_Util.fold_left
                                                               (fun uu___3 ->
                                                                  fun uu___2
                                                                    ->
                                                                    (fun t ->
                                                                    fun p ->
                                                                    match p
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax.Tm_Pure
                                                                    p1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    add_intro_pure
                                                                    p1 t))
                                                                    | 
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Impossible"))
                                                                    uu___3
                                                                    uu___2)
                                                               (Pulse_Syntax.Tm_Protect
                                                                  t0) pures))
                                                         (fun uu___2 ->
                                                            (fun t ->
                                                               let rec handle_intro_exists
                                                                 rest1 t1 =
                                                                 match rest1
                                                                 with
                                                                 | [] ->
                                                                    check f g
                                                                    t1 pre ()
                                                                    post_hint
                                                                 | (Pulse_Syntax.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p, se))::rest2
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (900))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (36)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (36)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax.Tm_Bind
                                                                    ((Pulse_Syntax.Tm_Protect
                                                                    (Pulse_Syntax.Tm_IntroExists
                                                                    (true,
                                                                    (Pulse_Syntax.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p, se)),
                                                                    []))),
                                                                    (Pulse_Syntax.Tm_Protect
                                                                    t1))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (handle_intro_exists
                                                                    rest2 t2))
                                                                    uu___2)
                                                                 | uu___2 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (911))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (911))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (911))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (911))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (911))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    t0))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (911))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (911))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (910))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (910))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (911))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (terms_to_string
                                                                    failure.Pulse_Checker_Framing.remaining_context))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (911))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (911))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (terms_to_string
                                                                    rest1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Failed to satisfy the following preconditions:\n"
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    "\nContext has\n"))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\nat command "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    uu___4))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___3) in
                                                               Obj.magic
                                                                 (handle_intro_exists
                                                                    rest t))
                                                              uu___2)))
                                               uu___1))) uu___))) uu___)
let rec (maybe_add_elims :
  Pulse_Typing.env ->
    Pulse_Syntax.term Prims.list ->
      Pulse_Syntax.st_term ->
        (Pulse_Syntax.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun ctxt ->
             fun t ->
               match ctxt with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
               | (Pulse_Syntax.Tm_ExistsSL (u, ty, b, se))::rest ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (923)) (Prims.of_int (14))
                              (Prims.of_int (923)) (Prims.of_int (64)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (924)) (Prims.of_int (6))
                              (Prims.of_int (930)) (Prims.of_int (30)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ ->
                                 Pulse_Syntax.Tm_Protect
                                   (Pulse_Syntax.Tm_ElimExists
                                      (Pulse_Syntax.Tm_ExistsSL
                                         (u, ty, b, se)))))
                           (fun uu___ ->
                              (fun e ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (924))
                                         (Prims.of_int (14))
                                         (Prims.of_int (924))
                                         (Prims.of_int (21)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (925))
                                         (Prims.of_int (6))
                                         (Prims.of_int (930))
                                         (Prims.of_int (30)))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___ -> Pulse_Typing.fresh g))
                                      (fun uu___ ->
                                         (fun x ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.fst"
                                                    (Prims.of_int (925))
                                                    (Prims.of_int (25))
                                                    (Prims.of_int (925))
                                                    (Prims.of_int (27)))
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.fst"
                                                    (Prims.of_int (926))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (930))
                                                    (Prims.of_int (30)))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___ ->
                                                       (x,
                                                         (FStar_Pervasives.Inl
                                                            ty))
                                                       :: g))
                                                 (fun uu___ ->
                                                    (fun g1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.fst"
                                                               (Prims.of_int (926))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (926))
                                                               (Prims.of_int (27)))
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.fst"
                                                               (Prims.of_int (927))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (930))
                                                               (Prims.of_int (30)))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___ ->
                                                                  Pulse_Syntax.open_term
                                                                    b x))
                                                            (fun uu___ ->
                                                               (fun b1 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (927))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (927))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (928))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (maybe_add_elims
                                                                    g1 [b1] t))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (928))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (928))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax.close_st_term
                                                                    t1 x))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax.Tm_Bind
                                                                    (e,
                                                                    (Pulse_Syntax.Tm_Protect
                                                                    t2))))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun t3
                                                                    ->
                                                                    Obj.magic
                                                                    (maybe_add_elims
                                                                    g1 rest
                                                                    t3))
                                                                    uu___)))
                                                                    uu___)))
                                                                    uu___)))
                                                                 uu___)))
                                                      uu___))) uu___))) uu___)))
               | (Pulse_Syntax.Tm_Pure p)::rest ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (932)) (Prims.of_int (25))
                              (Prims.of_int (934)) (Prims.of_int (35)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (936)) (Prims.of_int (6))
                              (Prims.of_int (937)) (Prims.of_int (53)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ ->
                                 Pulse_Syntax.Tm_STApp
                                   ((Pulse_Syntax.Tm_FVar
                                       elim_pure_explicit_lid),
                                     FStar_Pervasives_Native.None, p)))
                           (fun uu___ ->
                              (fun elim_pure_tm ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (937))
                                         (Prims.of_int (14))
                                         (Prims.of_int (937))
                                         (Prims.of_int (53)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (936))
                                         (Prims.of_int (6))
                                         (Prims.of_int (937))
                                         (Prims.of_int (53)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (937))
                                               (Prims.of_int (26))
                                               (Prims.of_int (937))
                                               (Prims.of_int (52)))
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (937))
                                               (Prims.of_int (14))
                                               (Prims.of_int (937))
                                               (Prims.of_int (53)))
                                            (Obj.magic
                                               (maybe_add_elims g rest t))
                                            (fun uu___ ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Pulse_Syntax.Tm_Protect
                                                      uu___))))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              Pulse_Syntax.Tm_Bind
                                                ((Pulse_Syntax.Tm_Protect
                                                    elim_pure_tm), uu___)))))
                                uu___)))
               | (Pulse_Syntax.Tm_Star (p, q))::rest ->
                   Obj.magic
                     (Obj.repr (maybe_add_elims g (p :: q :: rest) t))
               | uu___::rest ->
                   Obj.magic (Obj.repr (maybe_add_elims g rest t))) uu___2
          uu___1 uu___
let rec (unprotect : Pulse_Syntax.st_term -> Pulse_Syntax.st_term) =
  fun t ->
    match t with
    | Pulse_Syntax.Tm_Protect (Pulse_Syntax.Tm_Bind (e1, e2)) ->
        Pulse_Syntax.Tm_Bind ((Pulse_Syntax.Tm_Protect e1), e2)
    | Pulse_Syntax.Tm_Protect (Pulse_Syntax.Tm_If (b, then_, else_, post)) ->
        Pulse_Syntax.Tm_If
          (b, (Pulse_Syntax.Tm_Protect then_),
            (Pulse_Syntax.Tm_Protect else_), post)
    | Pulse_Syntax.Tm_Protect t1 -> unprotect t1
    | uu___ -> t
let (auto_elims :
  Pulse_Typing.env ->
    Pulse_Syntax.term ->
      Pulse_Syntax.st_term ->
        (Pulse_Syntax.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun ctxt ->
             fun t ->
               match t with
               | Pulse_Syntax.Tm_Protect uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> unprotect t)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (956)) (Prims.of_int (15))
                              (Prims.of_int (956)) (Prims.of_int (33)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (957)) (Prims.of_int (4))
                              (Prims.of_int (958)) (Prims.of_int (15)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Pulse_Checker_Framing.vprop_as_list ctxt))
                           (fun uu___1 ->
                              (fun ctxt1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (957))
                                         (Prims.of_int (12))
                                         (Prims.of_int (957))
                                         (Prims.of_int (36)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (958))
                                         (Prims.of_int (4))
                                         (Prims.of_int (958))
                                         (Prims.of_int (15)))
                                      (Obj.magic (maybe_add_elims g ctxt1 t))
                                      (fun t1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 -> unprotect t1))))
                                uu___1)))) uu___2 uu___1 uu___
let rec (print_st_head : Pulse_Syntax.st_term -> Prims.string) =
  fun t ->
    match t with
    | Pulse_Syntax.Tm_Abs (uu___, uu___1, uu___2, uu___3, uu___4) -> "Abs"
    | Pulse_Syntax.Tm_Protect p -> print_st_head p
    | Pulse_Syntax.Tm_Return (uu___, uu___1, p) -> print_head p
    | Pulse_Syntax.Tm_Bind (uu___, uu___1) -> "Bind"
    | Pulse_Syntax.Tm_If (uu___, uu___1, uu___2, uu___3) -> "If"
    | Pulse_Syntax.Tm_While (uu___, uu___1, uu___2) -> "While"
    | Pulse_Syntax.Tm_Admit (uu___, uu___1, uu___2, uu___3) -> "Admit"
    | Pulse_Syntax.Tm_Par (uu___, uu___1, uu___2, uu___3, uu___4, uu___5) ->
        "Par"
    | Pulse_Syntax.Tm_Rewrite (uu___, uu___1) -> "Rewrite"
    | Pulse_Syntax.Tm_WithLocal (uu___, uu___1) -> "WithLocal"
    | Pulse_Syntax.Tm_STApp (p, uu___, uu___1) -> print_head p
    | Pulse_Syntax.Tm_IntroExists (uu___, uu___1, uu___2) -> "IntroExists"
    | Pulse_Syntax.Tm_ElimExists uu___ -> "ElimExists"
and (print_head : Pulse_Syntax.term -> Prims.string) =
  fun t ->
    match t with
    | Pulse_Syntax.Tm_FVar fv -> FStar_String.concat "." fv
    | Pulse_Syntax.Tm_UInst (fv, uu___) -> FStar_String.concat "." fv
    | Pulse_Syntax.Tm_PureApp (head, uu___, uu___1) -> print_head head
    | uu___ -> "<pure term>"
let rec (print_skel : Pulse_Syntax.st_term -> Prims.string) =
  fun t ->
    match t with
    | Pulse_Syntax.Tm_Abs (uu___, uu___1, uu___2, body, uu___3) ->
        Prims.strcat "(fun _ -> " (Prims.strcat (print_skel body) ")")
    | Pulse_Syntax.Tm_Protect p ->
        Prims.strcat "(Protect " (Prims.strcat (print_skel p) ")")
    | Pulse_Syntax.Tm_Return (uu___, uu___1, p) -> print_head p
    | Pulse_Syntax.Tm_Bind (e1, e2) ->
        Prims.strcat
          (Prims.strcat "(Bind " (Prims.strcat (print_skel e1) " "))
          (Prims.strcat (print_skel e2) ")")
    | Pulse_Syntax.Tm_If (uu___, uu___1, uu___2, uu___3) -> "If"
    | Pulse_Syntax.Tm_While (uu___, uu___1, uu___2) -> "While"
    | Pulse_Syntax.Tm_Admit (uu___, uu___1, uu___2, uu___3) -> "Admit"
    | Pulse_Syntax.Tm_Par (uu___, uu___1, uu___2, uu___3, uu___4, uu___5) ->
        "Par"
    | Pulse_Syntax.Tm_Rewrite (uu___, uu___1) -> "Rewrite"
    | Pulse_Syntax.Tm_WithLocal (uu___, uu___1) -> "WithLocal"
    | Pulse_Syntax.Tm_STApp (p, uu___, uu___1) -> print_head p
    | Pulse_Syntax.Tm_IntroExists (uu___, uu___1, uu___2) -> "IntroExists"
    | Pulse_Syntax.Tm_ElimExists uu___ -> "ElimExists"
let (check_par :
  Prims.bool ->
    FStar_Reflection_Typing.fstar_top_env ->
      Pulse_Typing.env ->
        Pulse_Syntax.st_term ->
          Pulse_Syntax.term ->
            unit ->
              Pulse_Syntax.term FStar_Pervasives_Native.option ->
                (Prims.bool -> Pulse_Checker_Common.check_t) ->
                  ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                     (unit, unit, unit, unit) Pulse_Typing.st_typing)
                     FStar_Pervasives.dtuple3,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun f ->
      fun g ->
        fun t ->
          fun pre ->
            fun pre_typing ->
              fun post_hint ->
                fun check' ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (1015)) (Prims.of_int (43))
                       (Prims.of_int (1015)) (Prims.of_int (44)))
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (1015)) (Prims.of_int (2))
                       (Prims.of_int (1039)) (Prims.of_int (34)))
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t))
                    (fun uu___ ->
                       (fun uu___ ->
                          match uu___ with
                          | Pulse_Syntax.Tm_Par
                              (preL, eL, postL, preR, eR, postR) ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (1017))
                                      (Prims.of_int (4))
                                      (Prims.of_int (1017))
                                      (Prims.of_int (49)))
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (1016))
                                      (Prims.of_int (2))
                                      (Prims.of_int (1039))
                                      (Prims.of_int (34)))
                                   (Obj.magic
                                      (Pulse_Checker_Pure.check_tot_with_expected_typ
                                         f g preL Pulse_Syntax.Tm_VProp))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         match uu___1 with
                                         | Prims.Mkdtuple2
                                             (preL1, preL_typing) ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (1019))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (1019))
                                                     (Prims.of_int (49)))
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (1018))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (1039))
                                                     (Prims.of_int (34)))
                                                  (Obj.magic
                                                     (Pulse_Checker_Pure.check_tot_with_expected_typ
                                                        f g preR
                                                        Pulse_Syntax.Tm_VProp))
                                                  (fun uu___2 ->
                                                     (fun uu___2 ->
                                                        match uu___2 with
                                                        | Prims.Mkdtuple2
                                                            (preR1,
                                                             preR_typing)
                                                            ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1022))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1022))
                                                                    (Prims.of_int (62)))
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1021))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1039))
                                                                    (Prims.of_int (34)))
                                                                 (Obj.magic
                                                                    (
                                                                    check'
                                                                    allow_inst
                                                                    f g eL
                                                                    preL1 ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    postL)))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eL1, cL,
                                                                    eL_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax.uu___is_C_ST
                                                                    cL
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1028))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (1028))
                                                                    (Prims.of_int (53)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1029))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1038))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (check_comp
                                                                    f g cL ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    cL_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1030))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1030))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1029))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1038))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    f g eR
                                                                    preR1 ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    postR)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eR1, cR,
                                                                    eR_typing)
                                                                    ->
                                                                    if
                                                                    (Pulse_Syntax.uu___is_C_ST
                                                                    cR) &&
                                                                    ((Pulse_Syntax.comp_u
                                                                    cL) =
                                                                    (Pulse_Syntax.comp_u
                                                                    cR))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1034))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1034))
                                                                    (Prims.of_int (55)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1035))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1037))
                                                                    (Prims.of_int (56)))
                                                                    (Obj.magic
                                                                    (check_comp
                                                                    f g cR ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    cR_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1035))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1035))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1036))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1037))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1036))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1036))
                                                                    (Prims.of_int (71)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1037))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1037))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_Par
                                                                    (g, eL1,
                                                                    cL, eR1,
                                                                    cR, x,
                                                                    cL_typing,
                                                                    cR_typing,
                                                                    eL_typing,
                                                                    eR_typing)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1037))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1037))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1037))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1037))
                                                                    (Prims.of_int (56)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    f g
                                                                    (Pulse_Syntax.Tm_Par
                                                                    (Pulse_Syntax.Tm_Unknown,
                                                                    eL1,
                                                                    Pulse_Syntax.Tm_Unknown,
                                                                    Pulse_Syntax.Tm_Unknown,
                                                                    eR1,
                                                                    Pulse_Syntax.Tm_Unknown))
                                                                    pre ()
                                                                    (Pulse_Typing.comp_par
                                                                    cL cR x)
                                                                    d))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (repack f
                                                                    g pre
                                                                    (Pulse_Syntax.Tm_Par
                                                                    (Pulse_Syntax.Tm_Unknown,
                                                                    eL1,
                                                                    Pulse_Syntax.Tm_Unknown,
                                                                    Pulse_Syntax.Tm_Unknown,
                                                                    eR1,
                                                                    Pulse_Syntax.Tm_Unknown))
                                                                    uu___5
                                                                    post_hint
                                                                    true))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "par: cR is not stt")))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "par: cL is not stt")))
                                                                    uu___3)))
                                                       uu___2))) uu___1)))
                         uu___)
let (check_withlocal :
  Prims.bool ->
    FStar_Reflection_Typing.fstar_top_env ->
      Pulse_Typing.env ->
        Pulse_Syntax.st_term ->
          Pulse_Syntax.term ->
            unit ->
              Pulse_Syntax.term FStar_Pervasives_Native.option ->
                (Prims.bool -> Pulse_Checker_Common.check_t) ->
                  ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                     (unit, unit, unit, unit) Pulse_Typing.st_typing)
                     FStar_Pervasives.dtuple3,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun f ->
      fun g ->
        fun t ->
          fun pre ->
            fun pre_typing ->
              fun post_hint ->
                fun check' ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (1055)) (Prims.of_int (31))
                       (Prims.of_int (1055)) (Prims.of_int (32)))
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (1055)) (Prims.of_int (2))
                       (Prims.of_int (1092)) (Prims.of_int (57)))
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t))
                    (fun uu___ ->
                       (fun uu___ ->
                          match uu___ with
                          | Pulse_Syntax.Tm_WithLocal (init, body) ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (1057))
                                      (Prims.of_int (4))
                                      (Prims.of_int (1057))
                                      (Prims.of_int (27)))
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (1056))
                                      (Prims.of_int (2))
                                      (Prims.of_int (1092))
                                      (Prims.of_int (57)))
                                   (Obj.magic
                                      (Pulse_Checker_Pure.check_tot_univ f g
                                         init))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         match uu___1 with
                                         | FStar_Pervasives.Mkdtuple5
                                             (init1, init_u, init_t,
                                              init_t_typing, init_typing)
                                             ->
                                             if init_u = Pulse_Syntax.U_zero
                                             then
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (1059))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (1059))
                                                          (Prims.of_int (22)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (1060))
                                                          (Prims.of_int (7))
                                                          (Prims.of_int (1091))
                                                          (Prims.of_int (48)))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             Pulse_Typing.fresh
                                                               g))
                                                       (fun uu___2 ->
                                                          (fun x ->
                                                             if
                                                               FStar_Set.mem
                                                                 x
                                                                 (Pulse_Syntax.freevars_st
                                                                    body)
                                                             then
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Derived.fail
                                                                    "withlocal: x is free in body"))
                                                             else
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1063))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (1063))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1064))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (1091))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax.null_var
                                                                    x))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun x_tm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1064))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (1064))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1065))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (1091))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (x,
                                                                    (FStar_Pervasives.Inl
                                                                    (Pulse_Typing.mk_ref
                                                                    init_t)))
                                                                    :: g))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    g_extended
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1065))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (1065))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1066))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (1091))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.comp_withlocal_body_pre
                                                                    pre
                                                                    init_t
                                                                    x_tm
                                                                    init1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body_pre
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1066))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (1066))
                                                                    (Prims.of_int (74)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1069))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (1091))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    f
                                                                    g_extended
                                                                    body_pre))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body_pre_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1070))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1075))
                                                                    (Prims.of_int (36)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1076))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (1091))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1071))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1073))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1074))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1075))
                                                                    (Prims.of_int (36)))
                                                                    (match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    post)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "withlocal: no post_hint!")
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1074))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (1074))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1074))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1075))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop
                                                                    f
                                                                    g_extended
                                                                    (Pulse_Syntax.open_term
                                                                    post x)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened,
                                                                    uu___5)
                                                                    ->
                                                                    Pulse_Syntax.close_term
                                                                    post_opened
                                                                    x))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1076))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1076))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1077))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (1091))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.comp_withlocal_body_post
                                                                    post
                                                                    init_t
                                                                    x_tm))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body_post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1078))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1078))
                                                                    (Prims.of_int (105)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1077))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (1091))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    f
                                                                    g_extended
                                                                    (Pulse_Syntax.open_st_term
                                                                    body x)
                                                                    body_pre
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    body_post)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (opened_body,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    ((Pulse_Syntax.uu___is_C_ST
                                                                    c_body)
                                                                    &&
                                                                    (Pulse_Syntax.eq_tm
                                                                    (Pulse_Syntax.comp_post
                                                                    c_body)
                                                                    body_post))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "withlocal: body is not stt or postcondition mismatch"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1084))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1084))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1086))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1091))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax.close_st_term
                                                                    opened_body
                                                                    x))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1086))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1086))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1088))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1091))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax.C_ST
                                                                    {
                                                                    Pulse_Syntax.u
                                                                    =
                                                                    (Pulse_Syntax.comp_u
                                                                    c_body);
                                                                    Pulse_Syntax.res
                                                                    =
                                                                    (Pulse_Syntax.comp_res
                                                                    c_body);
                                                                    Pulse_Syntax.pre
                                                                    = pre;
                                                                    Pulse_Syntax.post
                                                                    = post
                                                                    }))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun c ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1088))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (1088))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1091))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1091))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (check_comp
                                                                    f g c ()))
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax.Tm_WithLocal
                                                                    (init1,
                                                                    body1)),
                                                                    c,
                                                                    (Pulse_Typing.T_WithLocal
                                                                    (g,
                                                                    init1,
                                                                    body1,
                                                                    init_t,
                                                                    c, x, (),
                                                                    (),
                                                                    c_typing,
                                                                    body_typing)))))))
                                                                    uu___5)))
                                                                    uu___5))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3))))
                                                            uu___2)))
                                             else
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Derived.fail
                                                       "withlocal: init type is not universe zero")))
                                        uu___1))) uu___)
let (check_rewrite :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        Pulse_Syntax.term ->
          unit ->
            Pulse_Syntax.term FStar_Pervasives_Native.option ->
              ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                 (unit, unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (1106)) (Prims.of_int (23))
                   (Prims.of_int (1106)) (Prims.of_int (24)))
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (1106)) (Prims.of_int (2))
                   (Prims.of_int (1116)) (Prims.of_int (52)))
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax.Tm_Rewrite (p, q) ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (1107)) (Prims.of_int (26))
                                  (Prims.of_int (1107)) (Prims.of_int (43)))
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (1107)) (Prims.of_int (2))
                                  (Prims.of_int (1116)) (Prims.of_int (52)))
                               (Obj.magic
                                  (Pulse_Checker_Pure.check_vprop f g p))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | Prims.Mkdtuple2 (p1, p_typing) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (1108))
                                                 (Prims.of_int (26))
                                                 (Prims.of_int (1108))
                                                 (Prims.of_int (43)))
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (1108))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (1116))
                                                 (Prims.of_int (52)))
                                              (Obj.magic
                                                 (Pulse_Checker_Pure.check_vprop
                                                    f g q))
                                              (fun uu___2 ->
                                                 (fun uu___2 ->
                                                    match uu___2 with
                                                    | Prims.Mkdtuple2
                                                        (q1, q_typing) ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (1110))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (1114))
                                                                (Prims.of_int (42)))
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (1115))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (1116))
                                                                (Prims.of_int (52)))
                                                             (if
                                                                Pulse_Syntax.eq_tm
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1112))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (1112))
                                                                    (Prims.of_int (75)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1112))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (1114))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.check_equiv
                                                                    (Pulse_Typing.extend_env_l
                                                                    f g)
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    p1)
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    q1)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "rewrite: p and q elabs are not equiv"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    token ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ())))))
                                                             (fun uu___3 ->
                                                                (fun
                                                                   equiv_p_q
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1115))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (1115))
                                                                    (Prims.of_int (44)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1116))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1116))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Rewrite
                                                                    (g, p1,
                                                                    q1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1116))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (1116))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1116))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1116))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    f g
                                                                    (Pulse_Syntax.Tm_Rewrite
                                                                    (p1, q1))
                                                                    pre ()
                                                                    (Pulse_Typing.comp_rewrite
                                                                    p1 q1) d))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (repack f
                                                                    g pre
                                                                    (Pulse_Syntax.Tm_Rewrite
                                                                    (p1, q1))
                                                                    uu___3
                                                                    post_hint
                                                                    true))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                  uu___3)))
                                                   uu___2))) uu___1))) uu___)
let rec (check' : Prims.bool -> Pulse_Checker_Common.check_t) =
  fun allow_inst ->
    fun f ->
      fun g ->
        fun t ->
          fun pre ->
            fun pre_typing ->
              fun post_hint ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (1128)) (Prims.of_int (4))
                     (Prims.of_int (1130)) (Prims.of_int (10)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (1132)) (Prims.of_int (2))
                     (Prims.of_int (1192)) (Prims.of_int (18)))
                  (if allow_inst
                   then Obj.magic (Obj.repr (auto_elims g pre t))
                   else
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 -> t))))
                  (fun uu___ ->
                     (fun t1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (1132)) (Prims.of_int (2))
                                (Prims.of_int (1132)) (Prims.of_int (53)))
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (1133)) (Prims.of_int (2))
                                (Prims.of_int (1192)) (Prims.of_int (18)))
                             (Obj.magic
                                (FStar_Tactics_Builtins.print
                                   (Prims.strcat "Check: "
                                      (Prims.strcat (print_skel t1) ""))))
                             (fun uu___ ->
                                (fun uu___ ->
                                   Obj.magic
                                     (FStar_Tactics_Derived.try_with
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match () with
                                              | () ->
                                                  (match t1 with
                                                   | Pulse_Syntax.Tm_Protect
                                                       uu___2 ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Derived.fail
                                                               "Protect should have been removed"))
                                                   | Pulse_Syntax.Tm_Return
                                                       (uu___2, uu___3,
                                                        Pulse_Syntax.Tm_BVar
                                                        uu___4)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Derived.fail
                                                               "not locally nameless"))
                                                   | Pulse_Syntax.Tm_Return
                                                       (uu___2, uu___3,
                                                        uu___4)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (check_return
                                                               allow_inst f g
                                                               t1 pre ()
                                                               post_hint))
                                                   | Pulse_Syntax.Tm_Abs
                                                       (uu___2, uu___3,
                                                        uu___4, uu___5,
                                                        uu___6)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (check_abs f g t1
                                                               pre ()
                                                               post_hint
                                                               (check' true)))
                                                   | Pulse_Syntax.Tm_STApp
                                                       (uu___2, uu___3,
                                                        uu___4)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (check_stapp
                                                               allow_inst f g
                                                               t1 pre ()
                                                               post_hint
                                                               check'))
                                                   | Pulse_Syntax.Tm_Bind
                                                       (uu___2, uu___3) ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (Pulse_Checker_Bind.check_bind
                                                               f g t1 pre ()
                                                               post_hint
                                                               (check' true)))
                                                   | Pulse_Syntax.Tm_If
                                                       (b, e1, e2, post_if)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (1154))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (1157))
                                                                  (Prims.of_int (69)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (1159))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (1159))
                                                                  (Prims.of_int (60)))
                                                               (match 
                                                                  (post_if,
                                                                    post_hint)
                                                                with
                                                                | (FStar_Pervasives_Native.None,
                                                                   FStar_Pervasives_Native.Some
                                                                   p) ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    p)
                                                                | (FStar_Pervasives_Native.Some
                                                                   p,
                                                                   FStar_Pervasives_Native.None)
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    p)
                                                                | (uu___2,
                                                                   uu___3) ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "Either two annotations for if post or none")
                                                               (fun uu___2 ->
                                                                  (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (check_if
                                                                    f g b e1
                                                                    e2 pre ()
                                                                    post
                                                                    (check'
                                                                    true)))
                                                                    uu___2)))
                                                   | Pulse_Syntax.Tm_ElimExists
                                                       uu___2 ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (check_elim_exists
                                                               f g t1 pre ()
                                                               post_hint))
                                                   | Pulse_Syntax.Tm_IntroExists
                                                       (uu___2, uu___3, [])
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (1167))
                                                                  (Prims.of_int (25))
                                                                  (Prims.of_int (1167))
                                                                  (Prims.of_int (59)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (1168))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (1170))
                                                                  (Prims.of_int (65)))
                                                               (Obj.magic
                                                                  (maybe_infer_intro_exists
                                                                    f g t1
                                                                    pre))
                                                               (fun uu___4 ->
                                                                  (fun
                                                                    unary_intros
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1168))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1170))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1170))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1168))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1168))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    unary_intros))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "Inferred unary_intros:\n"
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    "\n")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.print
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    f g
                                                                    unary_intros
                                                                    pre ()
                                                                    post_hint))
                                                                    uu___4)))
                                                                    uu___4)))
                                                   | Pulse_Syntax.Tm_IntroExists
                                                       (uu___2, uu___3,
                                                        (Pulse_Syntax.Tm_Unknown)::[])
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (1167))
                                                                  (Prims.of_int (25))
                                                                  (Prims.of_int (1167))
                                                                  (Prims.of_int (59)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (1168))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (1170))
                                                                  (Prims.of_int (65)))
                                                               (Obj.magic
                                                                  (maybe_infer_intro_exists
                                                                    f g t1
                                                                    pre))
                                                               (fun uu___4 ->
                                                                  (fun
                                                                    unary_intros
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1168))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1170))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1170))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1168))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1168))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    unary_intros))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "Inferred unary_intros:\n"
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    "\n")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.print
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    f g
                                                                    unary_intros
                                                                    pre ()
                                                                    post_hint))
                                                                    uu___4)))
                                                                    uu___4)))
                                                   | Pulse_Syntax.Tm_IntroExists
                                                       (uu___2, uu___3,
                                                        uu___4::uu___5::uu___6)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (1167))
                                                                  (Prims.of_int (25))
                                                                  (Prims.of_int (1167))
                                                                  (Prims.of_int (59)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (1168))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (1170))
                                                                  (Prims.of_int (65)))
                                                               (Obj.magic
                                                                  (maybe_infer_intro_exists
                                                                    f g t1
                                                                    pre))
                                                               (fun uu___7 ->
                                                                  (fun
                                                                    unary_intros
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1168))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1170))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1170))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1168))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1168))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (1169))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    unary_intros))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    "Inferred unary_intros:\n"
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    "\n")))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.print
                                                                    uu___7))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    f g
                                                                    unary_intros
                                                                    pre ()
                                                                    post_hint))
                                                                    uu___7)))
                                                                    uu___7)))
                                                   | Pulse_Syntax.Tm_IntroExists
                                                       (uu___2, uu___3,
                                                        uu___4)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (check_intro_exists_either
                                                               f g t1
                                                               FStar_Pervasives_Native.None
                                                               pre ()
                                                               post_hint))
                                                   | Pulse_Syntax.Tm_While
                                                       (uu___2, uu___3,
                                                        uu___4)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (check_while
                                                               allow_inst f g
                                                               t1 pre ()
                                                               post_hint
                                                               check'))
                                                   | Pulse_Syntax.Tm_Admit
                                                       (uu___2, uu___3,
                                                        uu___4, uu___5)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (check_admit f g
                                                               t1 pre ()
                                                               post_hint))
                                                   | Pulse_Syntax.Tm_Par
                                                       (uu___2, uu___3,
                                                        uu___4, uu___5,
                                                        uu___6, uu___7)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (check_par
                                                               allow_inst f g
                                                               t1 pre ()
                                                               post_hint
                                                               check'))
                                                   | Pulse_Syntax.Tm_WithLocal
                                                       (uu___2, uu___3) ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (check_withlocal
                                                               allow_inst f g
                                                               t1 pre ()
                                                               post_hint
                                                               check'))
                                                   | Pulse_Syntax.Tm_Rewrite
                                                       (uu___2, uu___3) ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (check_rewrite f
                                                               g t1 pre ()
                                                               post_hint))))
                                             uu___1)
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | Framing_failure failure ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (handle_framing_failure
                                                          f g t1 pre ()
                                                          post_hint failure
                                                          (check' true)))
                                              | e ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.raise
                                                          e))) uu___1)))
                                  uu___))) uu___)
let (check : Pulse_Checker_Common.check_t) = check' true
