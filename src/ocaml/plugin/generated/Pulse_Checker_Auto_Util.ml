open Prims
let (k_elab_unit :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      (unit, unit, unit, unit) Pulse_Checker_Common.continuation_elaborator)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun ctxt ->
           fun p ->
             fun r ->
               Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> r)))
        uu___1 uu___
let (k_elab_trans :
  Pulse_Typing.env ->
    Pulse_Typing.env ->
      Pulse_Typing.env ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit)
                Pulse_Checker_Common.continuation_elaborator ->
                (unit, unit, unit, unit)
                  Pulse_Checker_Common.continuation_elaborator ->
                  (unit, unit, unit, unit)
                    Pulse_Checker_Common.continuation_elaborator)
  =
  fun g0 ->
    fun g1 ->
      fun g2 ->
        fun ctxt0 ->
          fun ctxt1 ->
            fun ctxt2 ->
              fun k0 ->
                fun k1 ->
                  fun post_hint ->
                    fun res ->
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
                           (Prims.of_int (24)) (Prims.of_int (39))
                           (Prims.of_int (24)) (Prims.of_int (57)))
                        (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
                           (Prims.of_int (24)) (Prims.of_int (26))
                           (Prims.of_int (24)) (Prims.of_int (57)))
                        (Obj.magic (k1 post_hint res))
                        (fun uu___ ->
                           (fun uu___ -> Obj.magic (k0 post_hint uu___))
                             uu___)
let (comp_st_with_post :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp_st)
  =
  fun c ->
    fun post ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Syntax_Base.C_ST
            {
              Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
              Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
              Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
              Pulse_Syntax_Base.post = post
            }
      | Pulse_Syntax_Base.C_STGhost (i, st) ->
          Pulse_Syntax_Base.C_STGhost
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
                Pulse_Syntax_Base.post = post
              })
      | Pulse_Syntax_Base.C_STAtomic (i, st) ->
          Pulse_Syntax_Base.C_STAtomic
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
                Pulse_Syntax_Base.post = post
              })
let (st_equiv_post :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term ->
            unit -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          fun post ->
            fun veq ->
              let c' = comp_st_with_post c post in
              let uu___ =
                Pulse_Typing_Metatheory.st_comp_typing_inversion g
                  (Pulse_Syntax_Base.st_comp_of_comp c)
                  (Pulse_Typing_Metatheory.comp_typing_inversion g c
                     (Pulse_Typing_Metatheory.st_typing_correctness g t c d)) in
              match uu___ with
              | FStar_Pervasives.Mkdtuple4 (u_of, pre_typing, x, post_typing)
                  ->
                  let st_equiv =
                    Pulse_Typing.ST_VPropEquiv
                      (g, c, c', x, (), (), (), (), ()) in
                  Pulse_Typing.T_Equiv (g, t, c, c', d, st_equiv)
let (simplify_post :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t -> fun c -> fun d -> fun post -> st_equiv_post g t c d post ()
let (k_elab_equiv :
  Pulse_Typing.env ->
    Pulse_Typing.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit)
                Pulse_Checker_Common.continuation_elaborator ->
                unit ->
                  unit ->
                    (unit, unit, unit, unit)
                      Pulse_Checker_Common.continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt1 ->
        fun ctxt1' ->
          fun ctxt2 ->
            fun ctxt2' ->
              fun k ->
                fun d1 ->
                  fun d2 ->
                    fun post_hint ->
                      fun res ->
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
                             (Prims.of_int (73)) (Prims.of_int (68))
                             (Prims.of_int (76)) (Prims.of_int (39)))
                          (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
                             (Prims.of_int (77)) (Prims.of_int (10))
                             (Prims.of_int (107)) (Prims.of_int (9)))
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___ ->
                                FStar_Pervasives.Mkdtuple3
                                  (Pulse_Syntax_Base.Tm_Emp, (), ())))
                          (fun uu___ ->
                             (fun framing_token2 ->
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Auto.Util.fst"
                                        (Prims.of_int (78))
                                        (Prims.of_int (68))
                                        (Prims.of_int (80))
                                        (Prims.of_int (39)))
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Auto.Util.fst"
                                        (Prims.of_int (81))
                                        (Prims.of_int (10))
                                        (Prims.of_int (107))
                                        (Prims.of_int (9)))
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___ ->
                                           FStar_Pervasives.Mkdtuple3
                                             (Pulse_Syntax_Base.Tm_Emp, (),
                                               ())))
                                     (fun uu___ ->
                                        (fun framing_token1 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Auto.Util.fst"
                                                   (Prims.of_int (82))
                                                   (Prims.of_int (32))
                                                   (Prims.of_int (82))
                                                   (Prims.of_int (35)))
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Auto.Util.fst"
                                                   (Prims.of_int (81))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (107))
                                                   (Prims.of_int (9)))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___ -> res))
                                                (fun uu___ ->
                                                   (fun uu___ ->
                                                      match uu___ with
                                                      | FStar_Pervasives.Mkdtuple3
                                                          (st, c, st_d) ->
                                                          if
                                                            Prims.op_Negation
                                                              (Pulse_Syntax_Base.stateful_comp
                                                                 c)
                                                          then
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Derived.fail
                                                                    "Unexpected non-stateful comp in continuation elaborate"))
                                                          else
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (105)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (9)))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                                    g2
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c)
                                                                    (Pulse_Typing_Metatheory.comp_typing_inversion
                                                                    g2 c
                                                                    (Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g2 st c
                                                                    st_d))))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (uu___3,
                                                                    pre_typing,
                                                                    uu___4,
                                                                    uu___5)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (125)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (19)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Checker_Framing.apply_frame
                                                                    g2 st
                                                                    ctxt2 ()
                                                                    c st_d
                                                                    framing_token2))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c',
                                                                    st_d') ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (19)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    simplify_post
                                                                    g2 st c'
                                                                    st_d'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    st_d'1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (19)))
                                                                    (Obj.magic
                                                                    (k
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (st,
                                                                    (comp_st_with_post
                                                                    c'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)),
                                                                    st_d'1))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (st1, c1,
                                                                    st_d1) ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c1)
                                                                    then
                                                                    FStar_Tactics_Derived.fail
                                                                    "Unexpected non-stateful comp in continuation elaborate"
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match 
                                                                    Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                                    g1
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)
                                                                    (Pulse_Typing_Metatheory.comp_typing_inversion
                                                                    g1 c1
                                                                    (Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g1 st1 c1
                                                                    st_d1))
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (uu___10,
                                                                    pre_typing1,
                                                                    uu___11,
                                                                    uu___12)
                                                                    ->
                                                                    (match 
                                                                    Pulse_Checker_Framing.apply_frame
                                                                    g1 st1
                                                                    ctxt1' ()
                                                                    c1 st_d1
                                                                    framing_token1
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c'1,
                                                                    st_d'2)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (st1,
                                                                    (comp_st_with_post
                                                                    c'1
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c1)),
                                                                    (simplify_post
                                                                    g1 st1
                                                                    c'1
                                                                    st_d'2
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c1))))))))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___2))))
                                                     uu___))) uu___))) uu___)
let rec (canon_right_aux :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      (Pulse_Syntax_Base.vprop ->
         (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
        ->
        ((Pulse_Syntax_Base.vprop Prims.list,
           Pulse_Syntax_Base.vprop Prims.list, unit) FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun vps ->
             fun f ->
               match vps with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              FStar_Pervasives.Mkdtuple3 ([], [], ()))))
               | hd::rest ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "Pulse.Checker.Auto.Util.fst"
                              (Prims.of_int (117)) (Prims.of_int (7))
                              (Prims.of_int (117)) (Prims.of_int (11)))
                           (FStar_Range.mk_range
                              "Pulse.Checker.Auto.Util.fst"
                              (Prims.of_int (117)) (Prims.of_int (4))
                              (Prims.of_int (140)) (Prims.of_int (7)))
                           (Obj.magic (f hd))
                           (fun uu___ ->
                              (fun uu___ ->
                                 if uu___
                                 then
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Auto.Util.fst"
                                           (Prims.of_int (119))
                                           (Prims.of_int (35))
                                           (Prims.of_int (119))
                                           (Prims.of_int (59)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Auto.Util.fst"
                                           (Prims.of_int (118))
                                           (Prims.of_int (14))
                                           (Prims.of_int (134))
                                           (Prims.of_int (34)))
                                        (Obj.magic (canon_right_aux g rest f))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (vps', fvps, v_eq) ->
                                                    FStar_Pervasives.Mkdtuple3
                                                      (vps', (hd :: fvps),
                                                        ()))))
                                 else
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Auto.Util.fst"
                                           (Prims.of_int (137))
                                           (Prims.of_int (36))
                                           (Prims.of_int (137))
                                           (Prims.of_int (60)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Auto.Util.fst"
                                           (Prims.of_int (136))
                                           (Prims.of_int (14))
                                           (Prims.of_int (139))
                                           (Prims.of_int (33)))
                                        (Obj.magic (canon_right_aux g rest f))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                match uu___2 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (vps', pures, v_eq) ->
                                                    FStar_Pervasives.Mkdtuple3
                                                      ((hd :: vps'), pures,
                                                        ()))))) uu___))))
          uu___2 uu___1 uu___
let (canon_right :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        (Pulse_Syntax_Base.vprop ->
           (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
          ->
          ((Pulse_Syntax_Base.term, unit,
             (unit, unit, unit, unit)
               Pulse_Checker_Common.continuation_elaborator)
             FStar_Pervasives.dtuple3,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun f ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
               (Prims.of_int (147)) (Prims.of_int (16)) (Prims.of_int (147))
               (Prims.of_int (32)))
            (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
               (Prims.of_int (147)) (Prims.of_int (35)) (Prims.of_int (152))
               (Prims.of_int (104)))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_Checker_VPropEquiv.canon_vprop ctxt))
            (fun uu___ ->
               (fun ctxt' ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
                          (Prims.of_int (148)) (Prims.of_int (33))
                          (Prims.of_int (148)) (Prims.of_int (73)))
                       (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
                          (Prims.of_int (147)) (Prims.of_int (35))
                          (Prims.of_int (152)) (Prims.of_int (104)))
                       (Obj.magic
                          (canon_right_aux g
                             (Pulse_Checker_VPropEquiv.vprop_as_list ctxt) f))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               match uu___ with
                               | FStar_Pervasives.Mkdtuple3
                                   (vps', pures, veq) ->
                                   FStar_Pervasives.Mkdtuple3
                                     ((Pulse_Checker_VPropEquiv.list_as_vprop
                                         (FStar_List_Tot_Base.append vps'
                                            pures)), (),
                                       (k_elab_equiv g g ctxt ctxt ctxt
                                          (Pulse_Checker_VPropEquiv.list_as_vprop
                                             (FStar_List_Tot_Base.append vps'
                                                pures)) (k_elab_unit g ctxt)
                                          () ())))))) uu___)
let (continuation_elaborator_with_bind :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.st_term ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            unit ->
              ((Pulse_Syntax_Base.var,
                 (unit, unit, unit, unit)
                   Pulse_Checker_Common.continuation_elaborator)
                 Prims.dtuple2,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun ctxt ->
                   fun c1 ->
                     fun e1 ->
                       fun e1_typing ->
                         fun ctxt_pre1_typing ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   match Pulse_Typing.star_typing_inversion g
                                           ctxt
                                           (Pulse_Syntax_Base.comp_pre c1) ()
                                   with
                                   | (ctxt_typing, pre1_typing) ->
                                       (match Pulse_Checker_Framing.apply_frame
                                                g e1
                                                (Pulse_Syntax_Base.Tm_Star
                                                   (ctxt,
                                                     (Pulse_Syntax_Base.comp_pre
                                                        c1))) () c1 e1_typing
                                                (FStar_Pervasives.Mkdtuple3
                                                   (ctxt, (), ()))
                                        with
                                        | Prims.Mkdtuple2 (c11, e1_typing1)
                                            ->
                                            (match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                     g
                                                     (Pulse_Syntax_Base.st_comp_of_comp
                                                        c11)
                                                     (Pulse_Typing_Metatheory.comp_typing_inversion
                                                        g c11
                                                        (Pulse_Typing_Metatheory.st_typing_correctness
                                                           g e1 c11
                                                           e1_typing1))
                                             with
                                             | FStar_Pervasives.Mkdtuple4
                                                 (u_of_1, pre_typing, uu___1,
                                                  uu___2)
                                                 ->
                                                 Prims.Mkdtuple2
                                                   ((Pulse_Typing.fresh g),
                                                     ((fun post_hint ->
                                                         fun res ->
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Auto.Util.fst"
                                                                (Prims.of_int (185))
                                                                (Prims.of_int (34))
                                                                (Prims.of_int (185))
                                                                (Prims.of_int (37)))
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Auto.Util.fst"
                                                                (Prims.of_int (184))
                                                                (Prims.of_int (24))
                                                                (Prims.of_int (217))
                                                                (Prims.of_int (5)))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   -> res))
                                                             (fun uu___3 ->
                                                                (fun uu___3
                                                                   ->
                                                                   match uu___3
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives.Mkdtuple3
                                                                    (e2, c2,
                                                                    e2_typing)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c2)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Unexpected non-stateful comp in continuation elaborate"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (7)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    e2_typing))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    e2_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (7)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e2
                                                                    (Pulse_Typing.fresh
                                                                    g)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    (Pulse_Typing.fresh
                                                                    g)
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c2))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Impossible"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (88)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (7)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Bind.bind_res_and_post_typing
                                                                    g
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)
                                                                    (Pulse_Typing.fresh
                                                                    g)
                                                                    post_hint))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (t_typing,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (23)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (28)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Bind.mk_bind
                                                                    g
                                                                    (Pulse_Syntax_Base.Tm_Star
                                                                    (ctxt,
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c1))) e1
                                                                    e2_closed
                                                                    c11 c2
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    (Pulse_Typing.fresh
                                                                    g))
                                                                    e1_typing1
                                                                    ()
                                                                    e2_typing1
                                                                    () ()))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e, c,
                                                                    e_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e, c,
                                                                    e_typing)))))
                                                                    uu___6))))
                                                                    uu___5)))
                                                                    uu___5))))
                                                                  uu___3)))))))))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
type mk_t =
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
           (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple3 FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr
let (elim_one :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.vprop ->
        unit ->
          Pulse_Syntax_Base.st_term ->
            Pulse_Syntax_Base.comp ->
              (unit, unit, unit) Pulse_Typing.st_typing ->
                ((Pulse_Typing.env, Pulse_Syntax_Base.term, unit,
                   (unit, unit, unit, unit)
                     Pulse_Checker_Common.continuation_elaborator)
                   FStar_Pervasives.dtuple4,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun p ->
        fun ctxt_p_typing ->
          fun e1 ->
            fun c1 ->
              fun e1_typing ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
                     (Prims.of_int (233)) (Prims.of_int (30))
                     (Prims.of_int (233)) (Prims.of_int (65)))
                  (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
                     (Prims.of_int (231)) (Prims.of_int (65))
                     (Prims.of_int (247)) (Prims.of_int (34)))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Typing.star_typing_inversion g ctxt p ()))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | (ctxt_typing, p_typing) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Auto.Util.fst"
                                    (Prims.of_int (235)) (Prims.of_int (19))
                                    (Prims.of_int (235)) (Prims.of_int (81)))
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Auto.Util.fst"
                                    (Prims.of_int (233)) (Prims.of_int (68))
                                    (Prims.of_int (247)) (Prims.of_int (34)))
                                 (Obj.magic
                                    (continuation_elaborator_with_bind g ctxt
                                       c1 e1 e1_typing ()))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         match uu___1 with
                                         | Prims.Mkdtuple2 (x, k) ->
                                             FStar_Pervasives.Mkdtuple4
                                               ((Pulse_Typing.extend x
                                                   (FStar_Pervasives.Inl
                                                      (Pulse_Syntax_Base.comp_res
                                                         c1)) g),
                                                 (Pulse_Syntax_Base.Tm_Star
                                                    ((Pulse_Syntax_Naming.open_term_nv
                                                        (Pulse_Syntax_Base.comp_post
                                                           c1)
                                                        (Pulse_Syntax_Base.v_as_nv
                                                           x)), ctxt)), (),
                                                 k))))) uu___)
let rec (elim_all :
  Pulse_Typing.env ->
    (Pulse_Syntax_Base.vprop ->
       (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
      ->
      mk_t ->
        Pulse_Syntax_Base.term ->
          unit ->
            ((Pulse_Typing.env, Pulse_Syntax_Base.term, unit,
               (unit, unit, unit, unit)
                 Pulse_Checker_Common.continuation_elaborator)
               FStar_Pervasives.dtuple4,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g ->
               fun f ->
                 fun mk ->
                   fun ctxt ->
                     fun ctxt_typing ->
                       match ctxt with
                       | Pulse_Syntax_Base.Tm_Star (ctxt', p) ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Auto.Util.fst"
                                      (Prims.of_int (259))
                                      (Prims.of_int (25))
                                      (Prims.of_int (259))
                                      (Prims.of_int (71)))
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Auto.Util.fst"
                                      (Prims.of_int (258))
                                      (Prims.of_int (25))
                                      (Prims.of_int (274))
                                      (Prims.of_int (10)))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ ->
                                         Pulse_Typing.star_typing_inversion g
                                           ctxt' p ()))
                                   (fun uu___ ->
                                      (fun uu___ ->
                                         match uu___ with
                                         | (uu___1, p_typing) ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Auto.Util.fst"
                                                     (Prims.of_int (260))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (260))
                                                     (Prims.of_int (13)))
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Auto.Util.fst"
                                                     (Prims.of_int (260))
                                                     (Prims.of_int (7))
                                                     (Prims.of_int (274))
                                                     (Prims.of_int (10)))
                                                  (Obj.magic (f p))
                                                  (fun uu___2 ->
                                                     (fun uu___2 ->
                                                        if uu___2
                                                        then
                                                          Obj.magic
                                                            (Obj.repr
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (35)))
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (59)))
                                                                  (Obj.magic
                                                                    (mk g p
                                                                    ()))
                                                                  (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (e1, c1,
                                                                    e1_typing))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (elim_one
                                                                    g ctxt' p
                                                                    () e1 c1
                                                                    e1_typing))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g',
                                                                    uu___5,
                                                                    ctxt_typing',
                                                                    k) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Util.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (elim_all
                                                                    g' f mk
                                                                    uu___5 ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g'',
                                                                    ctxt'',
                                                                    ctxt_typing'',
                                                                    k') ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g'',
                                                                    ctxt'',
                                                                    (),
                                                                    (k_elab_trans
                                                                    g g' g''
                                                                    (Pulse_Syntax_Base.Tm_Star
                                                                    (ctxt',
                                                                    p))
                                                                    uu___5
                                                                    ctxt'' k
                                                                    k'))))))
                                                                    uu___4)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g, ctxt,
                                                                    (),
                                                                    (k_elab_unit
                                                                    g ctxt))))))
                                                                    uu___3)))
                                                        else
                                                          Obj.magic
                                                            (Obj.repr
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g, ctxt,
                                                                    (),
                                                                    (k_elab_unit
                                                                    g ctxt))))))
                                                       uu___2))) uu___)))
                       | uu___ ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      FStar_Pervasives.Mkdtuple4
                                        (g, ctxt, (), (k_elab_unit g ctxt))))))
              uu___4 uu___3 uu___2 uu___1 uu___
let (add_elims :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.vprop ->
         (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
        ->
        mk_t ->
          unit ->
            ((Pulse_Typing.env, Pulse_Syntax_Base.term, unit,
               (unit, unit, unit, unit)
                 Pulse_Checker_Common.continuation_elaborator)
               FStar_Pervasives.dtuple4,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun f ->
        fun mk ->
          fun ctxt_typing ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
                 (Prims.of_int (287)) (Prims.of_int (40))
                 (Prims.of_int (287)) (Prims.of_int (65)))
              (FStar_Range.mk_range "Pulse.Checker.Auto.Util.fst"
                 (Prims.of_int (287)) (Prims.of_int (4)) (Prims.of_int (291))
                 (Prims.of_int (55))) (Obj.magic (canon_right g ctxt () f))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | FStar_Pervasives.Mkdtuple3 (ctxt', ctxt'_typing, k) ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "Pulse.Checker.Auto.Util.fst"
                                (Prims.of_int (289)) (Prims.of_int (7))
                                (Prims.of_int (289)) (Prims.of_int (33)))
                             (FStar_Range.mk_range
                                "Pulse.Checker.Auto.Util.fst"
                                (Prims.of_int (287)) (Prims.of_int (68))
                                (Prims.of_int (291)) (Prims.of_int (55)))
                             (Obj.magic (elim_all g f mk ctxt' ()))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     match uu___1 with
                                     | FStar_Pervasives.Mkdtuple4
                                         (g', ctxt'', ctxt''_typing, k') ->
                                         FStar_Pervasives.Mkdtuple4
                                           (g', ctxt'', (),
                                             (k_elab_trans g g g' ctxt ctxt'
                                                ctxt'' k k')))))) uu___)