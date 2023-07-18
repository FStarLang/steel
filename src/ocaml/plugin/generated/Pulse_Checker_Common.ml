open Prims
let (format_failed_goal :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term Prims.list ->
      Pulse_Syntax_Base.term Prims.list ->
        (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun goal ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                   (Prims.of_int (13)) (Prims.of_int (39))
                   (Prims.of_int (13)) (Prims.of_int (83)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                   (Prims.of_int (13)) (Prims.of_int (86))
                   (Prims.of_int (28)) (Prims.of_int (21)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun ts ->
                  FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string
                    ts))
          (fun uu___ ->
             (fun terms_to_strings ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                              (Prims.of_int (14)) (Prims.of_int (24))
                              (Prims.of_int (16)) (Prims.of_int (40)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                              (Prims.of_int (17)) (Prims.of_int (4))
                              (Prims.of_int (28)) (Prims.of_int (21)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           fun ss ->
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Common.fst"
                                        (Prims.of_int (15))
                                        (Prims.of_int (18))
                                        (Prims.of_int (15))
                                        (Prims.of_int (102)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Common.fst"
                                        (Prims.of_int (14))
                                        (Prims.of_int (24))
                                        (Prims.of_int (16))
                                        (Prims.of_int (40)))))
                               (Obj.magic
                                  (FStar_Tactics_Util.fold_left
                                     (fun uu___2 ->
                                        fun uu___1 ->
                                          (fun uu___1 ->
                                             fun s ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       match uu___1 with
                                                       | (i, acc) ->
                                                           ((i +
                                                               Prims.int_one),
                                                             ((Prims.strcat
                                                                 (Prims.strcat
                                                                    ""
                                                                    (
                                                                    Prims.strcat
                                                                    (Prims.string_of_int
                                                                    i) ". "))
                                                                 (Prims.strcat
                                                                    s "")) ::
                                                             acc))))) uu___2
                                            uu___1) (Prims.int_one, []) ss))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       match uu___1 with
                                       | (uu___3, s) ->
                                           FStar_String.concat "\n  "
                                             (FStar_List_Tot_Base.rev s)))))
                     (fun uu___ ->
                        (fun numbered_list ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Common.fst"
                                         (Prims.of_int (18))
                                         (Prims.of_int (36))
                                         (Prims.of_int (18))
                                         (Prims.of_int (71)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Common.fst"
                                         (Prims.of_int (19))
                                         (Prims.of_int (2))
                                         (Prims.of_int (28))
                                         (Prims.of_int (21)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      fun ts ->
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Common.fst"
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (50))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (71)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Common.fst"
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (36))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (71)))))
                                          (Obj.magic (terms_to_strings ts))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                Obj.magic
                                                  (numbered_list uu___1))
                                               uu___1)))
                                (fun uu___ ->
                                   (fun format_terms ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Common.fst"
                                                    (Prims.of_int (28))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (28))
                                                    (Prims.of_int (21)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Common.fst"
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (28))
                                                    (Prims.of_int (21)))))
                                           (Obj.magic
                                              (Pulse_Typing_Env.env_to_string
                                                 g))
                                           (fun uu___ ->
                                              (fun uu___ ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Common.fst"
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (28))
                                                               (Prims.of_int (21)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Common.fst"
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (28))
                                                               (Prims.of_int (21)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (23)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (21)))))
                                                            (Obj.magic
                                                               (format_terms
                                                                  ctxt))
                                                            (fun uu___1 ->
                                                               (fun uu___1 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (format_terms
                                                                    goal))
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
                                                                    "Failed to prove the following goals:\n  "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    "\nThe remaining conjuncts in the separation logic context available for use are:\n  "))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\nThe typing context is:\n  "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
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
                                                uu___))) uu___))) uu___)))
               uu___)
let (mk_arrow :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun t ->
      FStar_Reflection_Typing.mk_arrow (Pulse_Elaborate_Pure.elab_term ty)
        FStar_Reflection_V2_Data.Q_Explicit
        (Pulse_Elaborate_Pure.elab_term t)
let (mk_abs :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun t ->
      FStar_Reflection_Typing.mk_abs (Pulse_Elaborate_Pure.elab_term ty)
        FStar_Reflection_V2_Data.Q_Explicit
        (Pulse_Elaborate_Pure.elab_term t)
let (intro_post_hint :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term ->
        (unit Pulse_Typing.post_hint_for_env, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ret_ty_opt ->
      fun post ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                   (Prims.of_int (40)) (Prims.of_int (10))
                   (Prims.of_int (40)) (Prims.of_int (17)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                   (Prims.of_int (40)) (Prims.of_int (20))
                   (Prims.of_int (52)) (Prims.of_int (109)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Typing_Env.fresh g))
          (fun uu___ ->
             (fun x ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                              (Prims.of_int (42)) (Prims.of_int (6))
                              (Prims.of_int (44)) (Prims.of_int (19)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                              (Prims.of_int (45)) (Prims.of_int (4))
                              (Prims.of_int (52)) (Prims.of_int (109)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           match ret_ty_opt with
                           | FStar_Pervasives_Native.None ->
                               Pulse_Syntax_Base.tm_fstar
                                 FStar_Reflection_Typing.unit_ty
                                 FStar_Range.range_0
                           | FStar_Pervasives_Native.Some t -> t))
                     (fun uu___ ->
                        (fun ret_ty ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Common.fst"
                                         (Prims.of_int (46))
                                         (Prims.of_int (18))
                                         (Prims.of_int (46))
                                         (Prims.of_int (56)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Common.fst"
                                         (Prims.of_int (45))
                                         (Prims.of_int (4))
                                         (Prims.of_int (52))
                                         (Prims.of_int (109)))))
                                (Obj.magic
                                   (Pulse_Checker_Pure.instantiate_term_implicits
                                      g ret_ty))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      match uu___ with
                                      | (ret_ty1, uu___1) ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Common.fst"
                                                        (Prims.of_int (47))
                                                        (Prims.of_int (27))
                                                        (Prims.of_int (47))
                                                        (Prims.of_int (53)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Common.fst"
                                                        (Prims.of_int (46))
                                                        (Prims.of_int (59))
                                                        (Prims.of_int (52))
                                                        (Prims.of_int (109)))))
                                               (Obj.magic
                                                  (Pulse_Checker_Pure.check_universe
                                                     g ret_ty1))
                                               (fun uu___2 ->
                                                  (fun uu___2 ->
                                                     match uu___2 with
                                                     | Prims.Mkdtuple2
                                                         (u, ty_typing) ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (119)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (109)))))
                                                              (Obj.magic
                                                                 (Pulse_Checker_Pure.check_vprop
                                                                    (
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    ret_ty1)
                                                                    (
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    x))))
                                                              (fun uu___3 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post1,
                                                                    post_typing)
                                                                    ->
                                                                    {
                                                                    Pulse_Typing.g
                                                                    = g;
                                                                    Pulse_Typing.ret_ty
                                                                    = ret_ty1;
                                                                    Pulse_Typing.u
                                                                    = u;
                                                                    Pulse_Typing.ty_typing
                                                                    = ();
                                                                    Pulse_Typing.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post1 x);
                                                                    Pulse_Typing.post_typing
                                                                    = ()
                                                                    }))))
                                                    uu___2))) uu___))) uu___)))
               uu___)
let (post_hint_from_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) Pulse_Typing_Metatheory.comp_typing_u ->
        unit Pulse_Typing.post_hint_for_env)
  =
  fun g ->
    fun c ->
      fun ct ->
        let st_comp_typing =
          Pulse_Typing_Metatheory.comp_typing_inversion g c ct in
        let uu___ =
          Pulse_Typing_Metatheory.st_comp_typing_inversion g
            (Pulse_Syntax_Base.st_comp_of_comp c) st_comp_typing in
        match uu___ with
        | FStar_Pervasives.Mkdtuple4 (ty_typing, pre_typing, x, post_typing)
            ->
            let p =
              {
                Pulse_Typing.g = g;
                Pulse_Typing.ret_ty = (Pulse_Syntax_Base.comp_res c);
                Pulse_Typing.u = (Pulse_Syntax_Base.comp_u c);
                Pulse_Typing.ty_typing = ();
                Pulse_Typing.post = (Pulse_Syntax_Base.comp_post c);
                Pulse_Typing.post_typing = ()
              } in
            p
type ('g, 'ctxt, 'gu, 'ctxtu) continuation_elaborator =
  unit Pulse_Typing.post_hint_opt ->
    (unit, unit, unit) Pulse_Typing_Combinators.st_typing_in_ctxt ->
      ((unit, unit, unit) Pulse_Typing_Combinators.st_typing_in_ctxt, 
        unit) FStar_Tactics_Effect.tac_repr
let (k_elab_unit :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (unit, unit, unit, unit) continuation_elaborator)
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
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit) continuation_elaborator ->
                (unit, unit, unit, unit) continuation_elaborator ->
                  (unit, unit, unit, unit) continuation_elaborator)
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
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Common.fst"
                                 (Prims.of_int (93)) (Prims.of_int (39))
                                 (Prims.of_int (93)) (Prims.of_int (57)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Common.fst"
                                 (Prims.of_int (93)) (Prims.of_int (26))
                                 (Prims.of_int (93)) (Prims.of_int (57)))))
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
  Pulse_Typing_Env.env ->
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
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t -> fun c -> fun d -> fun post -> st_equiv_post g t c d post ()

let (k_elab_equiv_continutation :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            (unit, unit, unit, unit) continuation_elaborator ->
              unit -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt ->
        fun ctxt1 ->
          fun ctxt2 ->
            fun k ->
              fun d ->
                fun post_hint ->
                  fun res ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                               (Prims.of_int (149)) (Prims.of_int (60))
                               (Prims.of_int (152)) (Prims.of_int (33)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                               (Prims.of_int (153)) (Prims.of_int (4))
                               (Prims.of_int (163)) (Prims.of_int (34)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            FStar_Pervasives.Mkdtuple3
                              (Pulse_Syntax_Base.tm_emp, (), ())))
                      (fun uu___ ->
                         (fun framing_token ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Common.fst"
                                          (Prims.of_int (154))
                                          (Prims.of_int (26))
                                          (Prims.of_int (154))
                                          (Prims.of_int (29)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Common.fst"
                                          (Prims.of_int (153))
                                          (Prims.of_int (4))
                                          (Prims.of_int (163))
                                          (Prims.of_int (34)))))
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
                                               (k post_hint
                                                  (FStar_Pervasives.Mkdtuple3
                                                     (st, c, st_d)))
                                           else
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Common.fst"
                                                           (Prims.of_int (158))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (158))
                                                           (Prims.of_int (95)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Common.fst"
                                                           (Prims.of_int (156))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (163))
                                                           (Prims.of_int (34)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                          g2
                                                          (Pulse_Syntax_Base.st_comp_of_comp
                                                             c)
                                                          (Pulse_Typing_Metatheory.comp_typing_inversion
                                                             g2 c
                                                             (Pulse_Typing_Metatheory.st_typing_correctness
                                                                g2 st c st_d))))
                                                  (fun uu___2 ->
                                                     (fun uu___2 ->
                                                        match uu___2 with
                                                        | FStar_Pervasives.Mkdtuple4
                                                            (uu___3,
                                                             pre_typing,
                                                             uu___4, uu___5)
                                                            ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (73)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (34)))))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Combinators.apply_frame
                                                                    g2 st
                                                                    ctxt1 ()
                                                                    c st_d
                                                                    framing_token))
                                                                 (fun uu___6
                                                                    ->
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (34)))))
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
                                                                    (k
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (st,
                                                                    (comp_st_with_post
                                                                    c'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)),
                                                                    st_d'1))))
                                                                    uu___7)))
                                                                    uu___6)))
                                                       uu___2))) uu___)))
                           uu___)

let (k_elab_equiv_prefix :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            (unit, unit, unit, unit) continuation_elaborator ->
              unit -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt1 ->
        fun ctxt2 ->
          fun ctxt ->
            fun k ->
              fun d ->
                fun post_hint ->
                  fun res ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                               (Prims.of_int (179)) (Prims.of_int (60))
                               (Prims.of_int (181)) (Prims.of_int (31)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                               (Prims.of_int (182)) (Prims.of_int (4))
                               (Prims.of_int (197)) (Prims.of_int (11)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            FStar_Pervasives.Mkdtuple3
                              (Pulse_Syntax_Base.tm_emp, (), ())))
                      (fun uu___ ->
                         (fun framing_token ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Common.fst"
                                          (Prims.of_int (183))
                                          (Prims.of_int (12))
                                          (Prims.of_int (183))
                                          (Prims.of_int (27)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Common.fst"
                                          (Prims.of_int (183))
                                          (Prims.of_int (30))
                                          (Prims.of_int (197))
                                          (Prims.of_int (11)))))
                                 (Obj.magic (k post_hint res))
                                 (fun res1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ ->
                                         match res1 with
                                         | FStar_Pervasives.Mkdtuple3
                                             (st, c, st_d) ->
                                             if
                                               Prims.op_Negation
                                                 (Pulse_Syntax_Base.stateful_comp
                                                    c)
                                             then
                                               FStar_Pervasives.Mkdtuple3
                                                 (st, c, st_d)
                                             else
                                               (match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                        g1
                                                        (Pulse_Syntax_Base.st_comp_of_comp
                                                           c)
                                                        (Pulse_Typing_Metatheory.comp_typing_inversion
                                                           g1 c
                                                           (Pulse_Typing_Metatheory.st_typing_correctness
                                                              g1 st c st_d))
                                                with
                                                | FStar_Pervasives.Mkdtuple4
                                                    (uu___2, pre_typing,
                                                     uu___3, uu___4)
                                                    ->
                                                    (match Pulse_Typing_Combinators.apply_frame
                                                             g1 st ctxt2 () c
                                                             st_d
                                                             framing_token
                                                     with
                                                     | Prims.Mkdtuple2
                                                         (c', st_d') ->
                                                         FStar_Pervasives.Mkdtuple3
                                                           (st,
                                                             (comp_st_with_post
                                                                c'
                                                                (Pulse_Syntax_Base.comp_post
                                                                   c)),
                                                             (simplify_post
                                                                g1 st c'
                                                                st_d'
                                                                (Pulse_Syntax_Base.comp_post
                                                                   c)))))))))
                           uu___)
let (k_elab_equiv :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit) continuation_elaborator ->
                unit ->
                  unit -> (unit, unit, unit, unit) continuation_elaborator)
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
                    let k1 =
                      k_elab_equiv_continutation g1 g2 ctxt1 ctxt2 ctxt2' k
                        () in
                    let k2 =
                      k_elab_equiv_prefix g1 g2 ctxt1 ctxt1' ctxt2' k1 () in
                    k2
let (continuation_elaborator_with_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.st_term ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            unit ->
              Pulse_Syntax_Base.var ->
                ((unit, unit, unit, unit) continuation_elaborator, unit)
                  FStar_Tactics_Effect.tac_repr)
  =
  fun uu___6 ->
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
                             fun x ->
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ ->
                                       match Pulse_Typing_Combinators.apply_frame
                                               g e1
                                               (Pulse_Syntax_Base.tm_star
                                                  ctxt
                                                  (Pulse_Syntax_Base.comp_pre
                                                     c1)) () c1 e1_typing
                                               (FStar_Pervasives.Mkdtuple3
                                                  (ctxt, (), ()))
                                       with
                                       | Prims.Mkdtuple2 (c11, e1_typing1) ->
                                           (match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                    g
                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                       c11)
                                                    (Pulse_Typing_Metatheory.comp_typing_inversion
                                                       g c11
                                                       (Pulse_Typing_Metatheory.st_typing_correctness
                                                          g e1 c11 e1_typing1))
                                            with
                                            | FStar_Pervasives.Mkdtuple4
                                                (u_of_1, pre_typing, uu___1,
                                                 uu___2)
                                                ->
                                                (fun post_hint ->
                                                   fun res ->
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Common.fst"
                                                                (Prims.of_int (243))
                                                                (Prims.of_int (34))
                                                                (Prims.of_int (243))
                                                                (Prims.of_int (37)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Common.fst"
                                                                (Prims.of_int (242))
                                                                (Prims.of_int (24))
                                                                (Prims.of_int (275))
                                                                (Prims.of_int (5)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 -> res))
                                                       (fun uu___3 ->
                                                          (fun uu___3 ->
                                                             match uu___3
                                                             with
                                                             | FStar_Pervasives.Mkdtuple3
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
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Unexpected non-stateful comp in continuation elaborate"))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (7)))))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e2 x))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c2))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Impossible"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Combinators.bind_res_and_post_typing
                                                                    g
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2) x
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Combinators.mk_bind
                                                                    g
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c1)) e1
                                                                    e2_closed
                                                                    c11 c2
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    x)
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
                                                            uu___3))))))
                  uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let rec (check_equiv_emp :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term -> unit FStar_Pervasives_Native.option)
  =
  fun g ->
    fun vp ->
      match vp.Pulse_Syntax_Base.t with
      | Pulse_Syntax_Base.Tm_Emp -> FStar_Pervasives_Native.Some ()
      | Pulse_Syntax_Base.Tm_Star (vp1, vp2) ->
          (match ((check_equiv_emp g vp1), (check_equiv_emp g vp2)) with
           | (FStar_Pervasives_Native.Some d1, FStar_Pervasives_Native.Some
              d2) -> FStar_Pervasives_Native.Some ()
           | (uu___, uu___1) -> FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None
type ('g, 'postuhint, 'x, 't, 'ctxtu) checker_res_matches_post_hint = Obj.t
type ('g, 'ctxt, 'postuhint) checker_result_t =
  (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term, Pulse_Syntax_Base.vprop,
    Pulse_Typing_Env.env, (unit, unit, unit, unit) continuation_elaborator)
    FStar_Pervasives.dtuple5
type check_t =
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.st_term ->
            ((unit, unit, unit) checker_result_t, unit)
              FStar_Tactics_Effect.tac_repr
let (intro_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      unit ->
        unit ->
          Pulse_Syntax_Base.var ->
            unit ->
              ((unit, unit, unit) Pulse_Typing.comp_typing, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c ->
      fun pre_typing ->
        fun res_typing ->
          fun x ->
            fun post_typing ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                         (Prims.of_int (384)) (Prims.of_int (8))
                         (Prims.of_int (384)) (Prims.of_int (52)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                         (Prims.of_int (386)) (Prims.of_int (4))
                         (Prims.of_int (401)) (Prims.of_int (44)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      fun uu___ ->
                        (fun uu___ ->
                           fun st ->
                             Obj.magic
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     Pulse_Typing.STC (g, st, x, (), (), ()))))
                          uu___1 uu___))
                (fun uu___ ->
                   (fun intro_st_comp_typing ->
                      match c with
                      | Pulse_Syntax_Base.C_ST st ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Common.fst"
                                        (Prims.of_int (388))
                                        (Prims.of_int (16))
                                        (Prims.of_int (388))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Common.fst"
                                        (Prims.of_int (389))
                                        (Prims.of_int (6))
                                        (Prims.of_int (389))
                                        (Prims.of_int (19)))))
                               (Obj.magic (intro_st_comp_typing st))
                               (fun stc ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ ->
                                       Pulse_Typing.CT_ST (g, st, stc))))
                      | Pulse_Syntax_Base.C_STAtomic (i, st) ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Common.fst"
                                        (Prims.of_int (391))
                                        (Prims.of_int (16))
                                        (Prims.of_int (391))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Common.fst"
                                        (Prims.of_int (391))
                                        (Prims.of_int (42))
                                        (Prims.of_int (395))
                                        (Prims.of_int (45)))))
                               (Obj.magic (intro_st_comp_typing st))
                               (fun uu___ ->
                                  (fun stc ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Common.fst"
                                                   (Prims.of_int (392))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (392))
                                                   (Prims.of_int (53)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Common.fst"
                                                   (Prims.of_int (391))
                                                   (Prims.of_int (42))
                                                   (Prims.of_int (395))
                                                   (Prims.of_int (45)))))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.core_check_term
                                                g i))
                                          (fun uu___ ->
                                             (fun uu___ ->
                                                match uu___ with
                                                | Prims.Mkdtuple2
                                                    (ty, i_typing) ->
                                                    if
                                                      Prims.op_Negation
                                                        (Pulse_Syntax_Base.eq_tm
                                                           ty
                                                           Pulse_Syntax_Base.tm_inames)
                                                    then
                                                      Obj.magic
                                                        (Obj.repr
                                                           (Pulse_Typing_Env.fail
                                                              g
                                                              FStar_Pervasives_Native.None
                                                              "Ill-typed inames"))
                                                    else
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 Pulse_Typing.CT_STAtomic
                                                                   (g, i, st,
                                                                    (), stc)))))
                                               uu___))) uu___))
                      | Pulse_Syntax_Base.C_STGhost (i, st) ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Common.fst"
                                        (Prims.of_int (397))
                                        (Prims.of_int (16))
                                        (Prims.of_int (397))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Common.fst"
                                        (Prims.of_int (397))
                                        (Prims.of_int (42))
                                        (Prims.of_int (401))
                                        (Prims.of_int (44)))))
                               (Obj.magic (intro_st_comp_typing st))
                               (fun uu___ ->
                                  (fun stc ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Common.fst"
                                                   (Prims.of_int (398))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (398))
                                                   (Prims.of_int (53)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Common.fst"
                                                   (Prims.of_int (397))
                                                   (Prims.of_int (42))
                                                   (Prims.of_int (401))
                                                   (Prims.of_int (44)))))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.core_check_term
                                                g i))
                                          (fun uu___ ->
                                             (fun uu___ ->
                                                match uu___ with
                                                | Prims.Mkdtuple2
                                                    (ty, i_typing) ->
                                                    if
                                                      Prims.op_Negation
                                                        (Pulse_Syntax_Base.eq_tm
                                                           ty
                                                           Pulse_Syntax_Base.tm_inames)
                                                    then
                                                      Obj.magic
                                                        (Obj.repr
                                                           (Pulse_Typing_Env.fail
                                                              g
                                                              FStar_Pervasives_Native.None
                                                              "Ill-typed inames"))
                                                    else
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 Pulse_Typing.CT_STGhost
                                                                   (g, i, st,
                                                                    (), stc)))))
                                               uu___))) uu___))) uu___)