open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (k_intro_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.binder ->
        Pulse_Syntax_Base.vprop ->
          unit ->
            Pulse_Syntax_Base.term ->
              unit ->
                Pulse_Syntax_Base.vprop ->
                  unit ->
                    ((unit, unit, unit, unit)
                       Pulse_Prover_Common.continuation_elaborator,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun u ->
      fun b ->
        fun p ->
          fun ex_typing ->
            fun e ->
              fun e_typing ->
                fun frame ->
                  fun frame_typing ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Pulse.Prover.IntroExists.fst"
                               (Prims.of_int (24)) (Prims.of_int (10))
                               (Prims.of_int (27)) (Prims.of_int (66)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Pulse.Prover.IntroExists.fst"
                               (Prims.of_int (27)) (Prims.of_int (69))
                               (Prims.of_int (65)) (Prims.of_int (30)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            Pulse_Typing.wr
                              (Pulse_Syntax_Base.Tm_IntroExists
                                 {
                                   Pulse_Syntax_Base.erased = false;
                                   Pulse_Syntax_Base.p2 =
                                     (Pulse_Syntax_Base.tm_exists_sl u b p);
                                   Pulse_Syntax_Base.witnesses = [e];
                                   Pulse_Syntax_Base.should_check1 =
                                     Pulse_Syntax_Base.should_check_true
                                 })))
                      (fun uu___ ->
                         (fun t ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.IntroExists.fst"
                                          (Prims.of_int (29))
                                          (Prims.of_int (10))
                                          (Prims.of_int (29))
                                          (Prims.of_int (35)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.IntroExists.fst"
                                          (Prims.of_int (29))
                                          (Prims.of_int (38))
                                          (Prims.of_int (65))
                                          (Prims.of_int (30)))))
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ ->
                                       Pulse_Typing.comp_intro_exists u b p e))
                                 (fun uu___ ->
                                    (fun c ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Prover.IntroExists.fst"
                                                     (Prims.of_int (31))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (31))
                                                     (Prims.of_int (70)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Prover.IntroExists.fst"
                                                     (Prims.of_int (34))
                                                     (Prims.of_int (45))
                                                     (Prims.of_int (65))
                                                     (Prims.of_int (30)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___ ->
                                                  Pulse_Typing.T_IntroExists
                                                    (g, u, b, p, e, (), (),
                                                      ())))
                                            (fun uu___ ->
                                               (fun t_typing ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Prover.IntroExists.fst"
                                                                (Prims.of_int (36))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (36))
                                                                (Prims.of_int (17)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Prover.IntroExists.fst"
                                                                (Prims.of_int (37))
                                                                (Prims.of_int (52))
                                                                (Prims.of_int (65))
                                                                (Prims.of_int (30)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___ ->
                                                             Pulse_Typing_Env.fresh
                                                               g))
                                                       (fun uu___ ->
                                                          (fun x ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (65)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                  (Obj.magic
                                                                    (Pulse_Prover_Common.continuation_elaborator_with_bind
                                                                    g frame
                                                                    (Pulse_Typing.comp_intro_exists
                                                                    u b p e)
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = false;
                                                                    Pulse_Syntax_Base.p2
                                                                    =
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b p);
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = [e];
                                                                    Pulse_Syntax_Base.should_check1
                                                                    =
                                                                    Pulse_Syntax_Base.should_check_true
                                                                    }))
                                                                    t_typing
                                                                    () x))
                                                                  (fun k ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    fun
                                                                    post_hint
                                                                    ->
                                                                    fun r ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    r))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t1, c1,
                                                                    d1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    d1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun d11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    empty_env
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Prover_Common.st_typing_weakening
                                                                    g
                                                                    empty_env
                                                                    t1 c1 d11
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun d12
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Prover_Common.k_elab_equiv
                                                                    g
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    frame
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    p
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    e)]))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    frame
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    p
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    e)]))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b p)
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    frame
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b p)) k
                                                                    () ()
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (t1, c1,
                                                                    d12))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___1)))))
                                                            uu___))) uu___)))
                                      uu___))) uu___)
let (intro_exists :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.binder ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop Prims.list ->
              unit ->
                Pulse_Prover_Common.prover_t ->
                  (unit Pulse_Prover_Common.prover_state, unit)
                    FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      fun u ->
        fun b ->
          fun body ->
            fun unsolved' ->
              fun uu___ ->
                fun prover ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "Pulse.Prover.IntroExists.fst"
                             (Prims.of_int (76)) (Prims.of_int (10))
                             (Prims.of_int (76)) (Prims.of_int (22)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "Pulse.Prover.IntroExists.fst"
                             (Prims.of_int (76)) (Prims.of_int (25))
                             (Prims.of_int (313)) (Prims.of_int (6)))))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          Pulse_Typing_Env.fresh pst.Pulse_Prover_Common.pg))
                    (fun uu___1 ->
                       (fun x ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.IntroExists.fst"
                                        (Prims.of_int (77))
                                        (Prims.of_int (11))
                                        (Prims.of_int (77))
                                        (Prims.of_int (29)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.IntroExists.fst"
                                        (Prims.of_int (77))
                                        (Prims.of_int (32))
                                        (Prims.of_int (313))
                                        (Prims.of_int (6)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     ((b.Pulse_Syntax_Base.binder_ppname), x)))
                               (fun uu___1 ->
                                  (fun px ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.IntroExists.fst"
                                                   (Prims.of_int (79))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (83))
                                                   (Prims.of_int (61)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.IntroExists.fst"
                                                   (Prims.of_int (84))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (313))
                                                   (Prims.of_int (6)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                {
                                                  Pulse_Prover_Common.g0 =
                                                    (pst.Pulse_Prover_Common.pg);
                                                  Pulse_Prover_Common.ctxt =
                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                       pst.Pulse_Prover_Common.remaining_ctxt);
                                                  Pulse_Prover_Common.frame =
                                                    (Pulse_Prover_Common.op_Star
                                                       preamble.Pulse_Prover_Common.frame
                                                       (Pulse_Prover_Common.op_Array_Access
                                                          pst.Pulse_Prover_Common.ss
                                                          pst.Pulse_Prover_Common.solved));
                                                  Pulse_Prover_Common.ctxt_frame_typing
                                                    = ();
                                                  Pulse_Prover_Common.goals =
                                                    (Pulse_Prover_Common.op_Star
                                                       (Pulse_Syntax_Naming.open_term_nv
                                                          body px)
                                                       (Pulse_Checker_VPropEquiv.list_as_vprop
                                                          unsolved'))
                                                }))
                                          (fun uu___1 ->
                                             (fun preamble_sub ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.IntroExists.fst"
                                                              (Prims.of_int (88))
                                                              (Prims.of_int (105))
                                                              (Prims.of_int (97))
                                                              (Prims.of_int (18)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.IntroExists.fst"
                                                              (Prims.of_int (99))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (313))
                                                              (Prims.of_int (6)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           coerce_eq
                                                             (Pulse_Prover_Common.k_elab_equiv
                                                                preamble_sub.Pulse_Prover_Common.g0
                                                                preamble_sub.Pulse_Prover_Common.g0
                                                                (Pulse_Prover_Common.op_Star
                                                                   preamble_sub.Pulse_Prover_Common.ctxt
                                                                   preamble_sub.Pulse_Prover_Common.frame)
                                                                (Pulse_Prover_Common.op_Star
                                                                   preamble_sub.Pulse_Prover_Common.ctxt
                                                                   preamble_sub.Pulse_Prover_Common.frame)
                                                                (Pulse_Prover_Common.op_Star
                                                                   preamble_sub.Pulse_Prover_Common.ctxt
                                                                   preamble_sub.Pulse_Prover_Common.frame)
                                                                (Pulse_Prover_Common.op_Star
                                                                   (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                    preamble_sub.Pulse_Prover_Common.ctxt))
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                   (Pulse_Prover_Common.op_Array_Access
                                                                    pst.Pulse_Prover_Common.ss
                                                                    Pulse_Syntax_Base.tm_emp))
                                                                (Pulse_Prover_Common.k_elab_unit
                                                                   preamble_sub.Pulse_Prover_Common.g0
                                                                   (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame))
                                                                () ()) ()))
                                                     (fun uu___1 ->
                                                        (fun k_sub ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (20)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___1 ->
                                                                    {
                                                                    Pulse_Prover_Common.pg
                                                                    =
                                                                    (pst.Pulse_Prover_Common.pg);
                                                                    Pulse_Prover_Common.remaining_ctxt
                                                                    =
                                                                    (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                    preamble_sub.Pulse_Prover_Common.ctxt);
                                                                    Pulse_Prover_Common.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Prover_Common.uvs
                                                                    =
                                                                    (pst.Pulse_Prover_Common.uvs);
                                                                    Pulse_Prover_Common.ss
                                                                    =
                                                                    (pst.Pulse_Prover_Common.ss);
                                                                    Pulse_Prover_Common.solved
                                                                    =
                                                                    Pulse_Syntax_Base.tm_emp;
                                                                    Pulse_Prover_Common.unsolved
                                                                    =
                                                                    (FStar_List_Tot_Base.append
                                                                    [
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    body px]
                                                                    unsolved');
                                                                    Pulse_Prover_Common.k
                                                                    = k_sub;
                                                                    Pulse_Prover_Common.goals_inv
                                                                    = ();
                                                                    Pulse_Prover_Common.solved_inv
                                                                    = ()
                                                                    }))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    pst_sub
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    (prover
                                                                    preamble_sub
                                                                    pst_sub))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    pst_sub1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    pst_sub_goals_inv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover_Substs.ss_to_nt_substs
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    pst_sub1.Pulse_Prover_Common.uvs
                                                                    pst_sub1.Pulse_Prover_Common.ss))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun ropt
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    ropt
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    FStar_Pervasives_Native.None
                                                                    "intro exists ss not well-typed"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ropt))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    nt ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    pst_sub_goals_inv1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    pst_sub_goals_inv2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    pst_sub_goals_inv3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    pst_sub1.Pulse_Prover_Common.k))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    k_sub1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Prover_Common.k_elab_equiv
                                                                    preamble_sub.Pulse_Prover_Common.g0
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    pst_sub1.Pulse_Prover_Common.solved))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    preamble_sub.Pulse_Prover_Common.goals))
                                                                    k_sub1 ()
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    k_sub2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    coerce_eq
                                                                    k_sub2 ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    k_sub3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    witness
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    coerce_eq
                                                                    k_sub3 ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    k_sub4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Prover_Common.k_elab_equiv
                                                                    preamble_sub.Pulse_Prover_Common.g0
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body)
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    witness)])
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved'))))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body)
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    k_sub4 ()
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    k_sub5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (k_intro_exists
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    u
                                                                    (Pulse_Prover_Substs.nt_subst_binder
                                                                    b nt)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body) ()
                                                                    witness
                                                                    ()
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))
                                                                    ()))
                                                                    (fun
                                                                    k_intro_exists1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    {
                                                                    Pulse_Prover_Common.pg
                                                                    =
                                                                    (pst_sub1.Pulse_Prover_Common.pg);
                                                                    Pulse_Prover_Common.remaining_ctxt
                                                                    =
                                                                    (pst_sub1.Pulse_Prover_Common.remaining_ctxt);
                                                                    Pulse_Prover_Common.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Prover_Common.uvs
                                                                    =
                                                                    (pst_sub1.Pulse_Prover_Common.uvs);
                                                                    Pulse_Prover_Common.ss
                                                                    =
                                                                    (pst_sub1.Pulse_Prover_Common.ss);
                                                                    Pulse_Prover_Common.solved
                                                                    =
                                                                    (preamble.Pulse_Prover_Common.goals);
                                                                    Pulse_Prover_Common.unsolved
                                                                    = [];
                                                                    Pulse_Prover_Common.k
                                                                    =
                                                                    (Pulse_Prover_Common.k_elab_equiv
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble.Pulse_Prover_Common.ctxt
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble.Pulse_Prover_Common.ctxt
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.unsolved))))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    preamble.Pulse_Prover_Common.goals))
                                                                    (Pulse_Prover_Common.k_elab_trans
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__pg
                                                                    preamble
                                                                    pst)
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble.Pulse_Prover_Common.ctxt
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__remaining_ctxt
                                                                    preamble
                                                                    pst))
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__ss
                                                                    preamble
                                                                    pst)
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__solved
                                                                    preamble
                                                                    pst)))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.unsolved))))
                                                                    pst.Pulse_Prover_Common.k
                                                                    (Pulse_Prover_Common.k_elab_equiv
                                                                    pst.Pulse_Prover_Common.pg
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.remaining_ctxt)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble.Pulse_Prover_Common.frame
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved)))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.unsolved))))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.unsolved))))
                                                                    (coerce_eq
                                                                    (Pulse_Prover_Common.k_elab_equiv
                                                                    preamble_sub.Pulse_Prover_Common.g0
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b body))
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved'))))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.unsolved))))
                                                                    (Pulse_Prover_Common.k_elab_trans
                                                                    preamble_sub.Pulse_Prover_Common.g0
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body)
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b body))
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved'))))
                                                                    k_sub5
                                                                    (coerce_eq
                                                                    (Pulse_Prover_Common.k_elab_equiv
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body)
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body)
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble.Pulse_Prover_Common.frame
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved)))
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b body)))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b body)))
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved'))))
                                                                    (coerce_eq
                                                                    k_intro_exists1
                                                                    ()) () ())
                                                                    ())) ()
                                                                    ()) ())
                                                                    () ()))
                                                                    () ());
                                                                    Pulse_Prover_Common.goals_inv
                                                                    = ();
                                                                    Pulse_Prover_Common.solved_inv
                                                                    = ()
                                                                    }))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                          uu___1))) uu___1)))
                                    uu___1))) uu___1)