open Prims
let (debug_log :
  Pulse_Typing_Env.env ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun f ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "st_app"
           then Obj.magic (Obj.repr (f ()))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let (canon_comp : Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.comp_st) =
  fun c ->
    match Pulse_Readback.readback_comp (Pulse_Elaborate_Pure.elab_comp c)
    with
    | FStar_Pervasives_Native.None -> c
    | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.C_Tot uu___) -> c
    | FStar_Pervasives_Native.Some c' -> c'
let (canon_comp_eq_res :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun c ->
      FStar_Reflection_Typing.Rel_refl
        ((Pulse_Typing.elab_env g),
          (Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_res c)),
          FStar_Reflection_Typing.R_Eq)
let (canonicalize_st_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          let c' = canon_comp c in
          let x = Pulse_Typing_Env.fresh g in
          let st_eq =
            Pulse_Typing.ST_VPropEquiv
              (g, c, c', x, (), (), (), (canon_comp_eq_res g c), (), ()) in
          Pulse_Typing.T_Equiv (g, t, c, c', d, st_eq)
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let rec (intro_uvars_for_logical_implicits :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          ((Pulse_Typing_Env.env, Pulse_Typing_Env.env,
             Pulse_Syntax_Base.st_term) FStar_Pervasives.dtuple3,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun t ->
        fun ty ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                     (Prims.of_int (49)) (Prims.of_int (13))
                     (Prims.of_int (49)) (Prims.of_int (24)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                     (Prims.of_int (50)) (Prims.of_int (2))
                     (Prims.of_int (69)) (Prims.of_int (31)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_Syntax_Pure.is_arrow ty))
            (fun uu___ ->
               (fun ropt ->
                  match ropt with
                  | FStar_Pervasives_Native.Some
                      (b, FStar_Pervasives_Native.Some
                       (Pulse_Syntax_Base.Implicit), c_rest)
                      ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (52)) (Prims.of_int (12))
                                    (Prims.of_int (52)) (Prims.of_int (34)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (52)) (Prims.of_int (37))
                                    (Prims.of_int (64)) (Prims.of_int (7)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ ->
                                 Pulse_Typing_Env.fresh
                                   (Pulse_Typing_Env.push_env g uvs)))
                           (fun uu___ ->
                              (fun x ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.STApp.fst"
                                               (Prims.of_int (53))
                                               (Prims.of_int (15))
                                               (Prims.of_int (53))
                                               (Prims.of_int (60)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.STApp.fst"
                                               (Prims.of_int (55))
                                               (Prims.of_int (6))
                                               (Prims.of_int (63))
                                               (Prims.of_int (96)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___ ->
                                            Pulse_Typing_Env.push_binding uvs
                                              x
                                              Pulse_Syntax_Base.ppname_default
                                              b.Pulse_Syntax_Base.binder_ty))
                                      (fun uu___ ->
                                         (fun uvs' ->
                                            match c_rest with
                                            | Pulse_Syntax_Base.C_ST uu___ ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           FStar_Pervasives.Mkdtuple3
                                                             (uvs',
                                                               (Pulse_Typing_Env.push_env
                                                                  g uvs'),
                                                               {
                                                                 Pulse_Syntax_Base.term1
                                                                   =
                                                                   (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = t;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit);
                                                                    Pulse_Syntax_Base.arg
                                                                    =
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x)
                                                                    });
                                                                 Pulse_Syntax_Base.range2
                                                                   =
                                                                   (t.Pulse_Syntax_Base.range1);
                                                                 Pulse_Syntax_Base.effect_tag
                                                                   =
                                                                   (Pulse_Syntax_Base.as_effect_hint
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c_rest))
                                                               }))))
                                            | Pulse_Syntax_Base.C_STAtomic
                                                (uu___, uu___1) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           FStar_Pervasives.Mkdtuple3
                                                             (uvs',
                                                               (Pulse_Typing_Env.push_env
                                                                  g uvs'),
                                                               {
                                                                 Pulse_Syntax_Base.term1
                                                                   =
                                                                   (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = t;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit);
                                                                    Pulse_Syntax_Base.arg
                                                                    =
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x)
                                                                    });
                                                                 Pulse_Syntax_Base.range2
                                                                   =
                                                                   (t.Pulse_Syntax_Base.range1);
                                                                 Pulse_Syntax_Base.effect_tag
                                                                   =
                                                                   (Pulse_Syntax_Base.as_effect_hint
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c_rest))
                                                               }))))
                                            | Pulse_Syntax_Base.C_STGhost
                                                (uu___, uu___1) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           FStar_Pervasives.Mkdtuple3
                                                             (uvs',
                                                               (Pulse_Typing_Env.push_env
                                                                  g uvs'),
                                                               {
                                                                 Pulse_Syntax_Base.term1
                                                                   =
                                                                   (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = t;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit);
                                                                    Pulse_Syntax_Base.arg
                                                                    =
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x)
                                                                    });
                                                                 Pulse_Syntax_Base.range2
                                                                   =
                                                                   (t.Pulse_Syntax_Base.range1);
                                                                 Pulse_Syntax_Base.effect_tag
                                                                   =
                                                                   (Pulse_Syntax_Base.as_effect_hint
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c_rest))
                                                               }))))
                                            | Pulse_Syntax_Base.C_Tot ty1 ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (intro_uvars_for_logical_implicits
                                                        g uvs'
                                                        (Pulse_Syntax_Pure.tm_pureapp
                                                           t
                                                           (FStar_Pervasives_Native.Some
                                                              Pulse_Syntax_Base.Implicit)
                                                           (Pulse_Syntax_Pure.null_var
                                                              x)) ty1)))
                                           uu___))) uu___))
                  | uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (67)) (Prims.of_int (6))
                                    (Prims.of_int (69)) (Prims.of_int (31)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (66)) (Prims.of_int (4))
                                    (Prims.of_int (69)) (Prims.of_int (31)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.STApp.fst"
                                          (Prims.of_int (69))
                                          (Prims.of_int (9))
                                          (Prims.of_int (69))
                                          (Prims.of_int (30)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "prims.fst"
                                          (Prims.of_int (590))
                                          (Prims.of_int (19))
                                          (Prims.of_int (590))
                                          (Prims.of_int (31)))))
                                 (Obj.magic
                                    (Pulse_Syntax_Printer.term_to_string ty))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         Prims.strcat
                                           "check_stapp.intro_uvars_for_logical_implicits: expected an arrow type,with an implicit parameter, found: "
                                           (Prims.strcat uu___1 "")))))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (Pulse_Typing_Env.fail g
                                      FStar_Pervasives_Native.None uu___1))
                                uu___1))) uu___)
let (instantiate_implicits :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      ((Pulse_Typing_Env.env, Pulse_Typing_Env.env,
         Pulse_Syntax_Base.st_term) FStar_Pervasives.dtuple3,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                 (Prims.of_int (77)) (Prims.of_int (14)) (Prims.of_int (77))
                 (Prims.of_int (21)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                 (Prims.of_int (77)) (Prims.of_int (24)) (Prims.of_int (93))
                 (Prims.of_int (32)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> t.Pulse_Syntax_Base.range2))
        (fun uu___ ->
           (fun range ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                            (Prims.of_int (78)) (Prims.of_int (46))
                            (Prims.of_int (78)) (Prims.of_int (52)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                            (Prims.of_int (77)) (Prims.of_int (24))
                            (Prims.of_int (93)) (Prims.of_int (32)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> t.Pulse_Syntax_Base.term1))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | Pulse_Syntax_Base.Tm_STApp
                             { Pulse_Syntax_Base.head = head;
                               Pulse_Syntax_Base.arg_qual = qual;
                               Pulse_Syntax_Base.arg = arg;_}
                             ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.STApp.fst"
                                           (Prims.of_int (79))
                                           (Prims.of_int (17))
                                           (Prims.of_int (79))
                                           (Prims.of_int (41)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.STApp.fst"
                                           (Prims.of_int (79))
                                           (Prims.of_int (44))
                                           (Prims.of_int (93))
                                           (Prims.of_int (32)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        Pulse_Syntax_Pure.tm_pureapp head
                                          qual arg))
                                  (fun uu___1 ->
                                     (fun pure_app ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.STApp.fst"
                                                      (Prims.of_int (80))
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (80))
                                                      (Prims.of_int (51)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.STApp.fst"
                                                      (Prims.of_int (79))
                                                      (Prims.of_int (44))
                                                      (Prims.of_int (93))
                                                      (Prims.of_int (32)))))
                                             (Obj.magic
                                                (Pulse_Checker_Pure.instantiate_term_implicits
                                                   g pure_app))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match uu___1 with
                                                   | (t1, ty) ->
                                                       (match Pulse_Syntax_Pure.is_arrow
                                                                ty
                                                        with
                                                        | FStar_Pervasives_Native.Some
                                                            (uu___2,
                                                             FStar_Pervasives_Native.Some
                                                             (Pulse_Syntax_Base.Implicit),
                                                             uu___3)
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (intro_uvars_for_logical_implicits
                                                                    g
                                                                    (
                                                                    Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)) t1 ty))
                                                        | uu___2 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (match 
                                                                    Pulse_Syntax_Pure.is_pure_app
                                                                    t1
                                                                  with
                                                                  | FStar_Pervasives_Native.Some
                                                                    (head1,
                                                                    q, arg1)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)),
                                                                    (Pulse_Typing_Env.push_env
                                                                    g
                                                                    (Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g))),
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = q;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (t1.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    Pulse_Syntax_Base.default_effect_hint
                                                                    })))
                                                                  | uu___3 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (31)))))
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
                                                                    t1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "check_stapp.instantiate_implicits: expected an application term, found: "
                                                                    (Prims.strcat
                                                                    uu___4 "")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t1.Pulse_Syntax_Base.range1))
                                                                    uu___4))
                                                                    uu___4))))))
                                                  uu___1))) uu___1))) uu___)))
             uu___)
let (apply_impure_function :
  Pulse_Syntax_Base.range ->
    Pulse_Typing_Env.env ->
      Pulse_Typing_Env.env ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              unit Pulse_Typing.post_hint_opt ->
                Pulse_Syntax_Base.ppname ->
                  Pulse_Syntax_Base.term ->
                    Pulse_Syntax_Base.qualifier
                      FStar_Pervasives_Native.option ->
                      Pulse_Syntax_Base.term ->
                        Pulse_Syntax_Base.term ->
                          FStar_TypeChecker_Core.tot_or_ghost ->
                            unit ->
                              (Pulse_Syntax_Base.binder *
                                Pulse_Syntax_Base.qualifier
                                FStar_Pervasives_Native.option *
                                Pulse_Syntax_Base.comp) ->
                                ((unit, unit, unit)
                                   Pulse_Checker_Base.checker_result_t,
                                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun range ->
    fun g0 ->
      fun uvs ->
        fun g ->
          fun ctxt ->
            fun ctxt_typing ->
              fun post_hint ->
                fun res_ppname ->
                  fun head ->
                    fun qual ->
                      fun arg ->
                        fun ty_head ->
                          fun eff_head ->
                            fun dhead ->
                              fun b ->
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.STApp.fst"
                                           (Prims.of_int (113))
                                           (Prims.of_int (67))
                                           (Prims.of_int (113))
                                           (Prims.of_int (68)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.STApp.fst"
                                           (Prims.of_int (113))
                                           (Prims.of_int (3))
                                           (Prims.of_int (186))
                                           (Prims.of_int (5)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ -> b))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        match uu___ with
                                        | ({
                                             Pulse_Syntax_Base.binder_ty =
                                               formal;
                                             Pulse_Syntax_Base.binder_ppname
                                               = ppname;_},
                                           bqual, comp_typ) ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.STApp.fst"
                                                          (Prims.of_int (115))
                                                          (Prims.of_int (38))
                                                          (Prims.of_int (115))
                                                          (Prims.of_int (47)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.STApp.fst"
                                                          (Prims.of_int (117))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (186))
                                                          (Prims.of_int (5)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 -> post_hint))
                                                 (fun uu___1 ->
                                                    (fun post_hint1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (46)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (5)))))
                                                            (Obj.magic
                                                               (debug_log g
                                                                  (fun uu___1
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (119))
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
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    comp_typ))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "st_app, readback comp as "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    "\n")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___2))
                                                                    uu___2))))
                                                            (fun uu___1 ->
                                                               (fun uu___1 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.uu___is_C_STGhost
                                                                    comp_typ))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    allow_ghost
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (5)))))
                                                                    (if
                                                                    (Prims.op_Negation
                                                                    allow_ghost)
                                                                    &&
                                                                    (eff_head
                                                                    =
                                                                    FStar_TypeChecker_Core.E_Ghost)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (37)))))
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
                                                                    head))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "head term "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " is ghost, but the arrow comp is not STGhost")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    range)
                                                                    uu___2))
                                                                    uu___2)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    if
                                                                    qual <>
                                                                    bqual
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    arg))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (131))
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
                                                                    ty_head))
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
                                                                    "Unexpected qualifier in head type "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    " of stateful application: head = "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", arg = "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
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
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    range)
                                                                    uu___3))
                                                                    uu___3))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (144)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    if
                                                                    allow_ghost
                                                                    then
                                                                    FStar_TypeChecker_Core.E_Ghost
                                                                    else
                                                                    FStar_TypeChecker_Core.E_Total))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    eff_arg
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (144)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type_and_effect
                                                                    g arg
                                                                    eff_arg
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (144)))))
                                                                    (match comp_typ
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_ST
                                                                    res ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ({
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    = range;
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    comp_typ))
                                                                    },
                                                                    (canon_comp
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)),
                                                                    (canonicalize_st_typing
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    comp_typ
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)
                                                                    (Pulse_Typing.T_STApp
                                                                    (g, head,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))))))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___5,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ({
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    = range;
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    comp_typ))
                                                                    },
                                                                    (canon_comp
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)),
                                                                    (canonicalize_st_typing
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    comp_typ
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)
                                                                    (Pulse_Typing.T_STApp
                                                                    (g, head,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))))))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (uu___5,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (23)))))
                                                                    (if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars_comp
                                                                    comp_typ)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    range)
                                                                    "Unexpected clash of variable names, please file a bug-report"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.is_non_informative
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    formal)
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    token ->
                                                                    match token
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
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (103)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (103)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (102)))))
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
                                                                    comp_typ))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    "Unexpected non-informative result for "
                                                                    (Prims.strcat
                                                                    uu___7 "")))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    range)
                                                                    uu___7))
                                                                    uu___7)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    token1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Reflection_Typing.Non_informative_token
                                                                    ((Pulse_Typing.elab_env
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    formal)),
                                                                    (Pulse_Elaborate_Pure.elab_comp
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x))), ())))))
                                                                    uu___7)))
                                                                    (fun
                                                                    d_non_info
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ({
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    = range;
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    Pulse_Syntax_Base.STT_Ghost)
                                                                    },
                                                                    (canon_comp
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)),
                                                                    (canonicalize_st_typing
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    comp_typ
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)
                                                                    (Pulse_Typing.T_STGhostApp
                                                                    (g, head,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, x,
                                                                    (), (),
                                                                    ()))))))))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    range)
                                                                    "Expected an effectful application; got a pure term (could it be partially applied by mistake?)")))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (144)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (144)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (128)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (144)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (116)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (128)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g t c d
                                                                    post_hint1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre_uvs
                                                                    g0 ctxt
                                                                    () uvs
                                                                    uu___7
                                                                    res_ppname))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g0 ctxt
                                                                    uu___7
                                                                    post_hint1
                                                                    range))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                 uu___1)))
                                                      uu___1))) uu___)
let (norm_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      FStar_TypeChecker_Core.tot_or_ghost ->
        Pulse_Syntax_Base.term ->
          unit ->
            FStar_Pervasives.norm_step Prims.list ->
              ((Pulse_Syntax_Base.term, unit) Prims.dtuple2, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun eff ->
        fun t0 ->
          fun d ->
            fun steps ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                         (Prims.of_int (194)) (Prims.of_int (12))
                         (Prims.of_int (194)) (Prims.of_int (24)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                         (Prims.of_int (194)) (Prims.of_int (27))
                         (Prims.of_int (216)) (Prims.of_int (18)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Pulse_Elaborate_Pure.elab_term t0))
                (fun uu___ ->
                   (fun t ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (196)) (Prims.of_int (6))
                                    (Prims.of_int (196)) (Prims.of_int (58)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (197)) (Prims.of_int (6))
                                    (Prims.of_int (216)) (Prims.of_int (18)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> ()))
                           (fun uu___ ->
                              (fun u_t_typing ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.STApp.fst"
                                               (Prims.of_int (199))
                                               (Prims.of_int (6))
                                               (Prims.of_int (199))
                                               (Prims.of_int (80)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.STApp.fst"
                                               (Prims.of_int (197))
                                               (Prims.of_int (6))
                                               (Prims.of_int (216))
                                               (Prims.of_int (18)))))
                                      (Obj.magic
                                         (Pulse_RuntimeUtils.norm_well_typed_term
                                            (Pulse_Typing.elab_env g)
                                            (Pulse_Elaborate_Pure.elab_term
                                               t0)
                                            FStar_TypeChecker_Core.E_Total ()
                                            ()
                                            [FStar_Pervasives.weak;
                                            FStar_Pervasives.hnf;
                                            FStar_Pervasives.delta]))
                                      (fun uu___ ->
                                         match uu___ with
                                         | FStar_Pervasives.Mkdtuple3
                                             (t', t'_typing, related_t_t') ->
                                             (match Pulse_Readback.readback_ty
                                                      t'
                                              with
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  FStar_Tactics_V2_Derived.fail
                                                    "Could not readback normalized type"
                                              | FStar_Pervasives_Native.Some
                                                  t'' ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       Prims.Mkdtuple2
                                                         (t'', ())))))) uu___)))
                     uu___)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g0 ->
    fun ctxt ->
      fun ctxt_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                         (Prims.of_int (227)) (Prims.of_int (11))
                         (Prims.of_int (227)) (Prims.of_int (43)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                         (Prims.of_int (227)) (Prims.of_int (46))
                         (Prims.of_int (258)) (Prims.of_int (117)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Checker_Pure.push_context "st_app"
                        t.Pulse_Syntax_Base.range2 g0))
                (fun uu___ ->
                   (fun g01 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (228)) (Prims.of_int (14))
                                    (Prims.of_int (228)) (Prims.of_int (21)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (228)) (Prims.of_int (24))
                                    (Prims.of_int (258)) (Prims.of_int (117)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> t.Pulse_Syntax_Base.range2))
                           (fun uu___ ->
                              (fun range ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.STApp.fst"
                                               (Prims.of_int (230))
                                               (Prims.of_int (24))
                                               (Prims.of_int (230))
                                               (Prims.of_int (50)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.STApp.fst"
                                               (Prims.of_int (228))
                                               (Prims.of_int (24))
                                               (Prims.of_int (258))
                                               (Prims.of_int (117)))))
                                      (Obj.magic
                                         (instantiate_implicits g01 t))
                                      (fun uu___ ->
                                         (fun uu___ ->
                                            match uu___ with
                                            | FStar_Pervasives.Mkdtuple3
                                                (uvs, g, t1) ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.STApp.fst"
                                                              (Prims.of_int (232))
                                                              (Prims.of_int (36))
                                                              (Prims.of_int (232))
                                                              (Prims.of_int (45)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.STApp.fst"
                                                              (Prims.of_int (232))
                                                              (Prims.of_int (48))
                                                              (Prims.of_int (258))
                                                              (Prims.of_int (117)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           post_hint))
                                                     (fun uu___1 ->
                                                        (fun post_hint1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (52)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (117)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___1 ->
                                                                    t1.Pulse_Syntax_Base.term1))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (117)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term
                                                                    g head))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (head1,
                                                                    eff_head,
                                                                    ty_head,
                                                                    dhead) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (117)))))
                                                                    (Obj.magic
                                                                    (debug_log
                                                                    g
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty_head))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (240))
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
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head1))
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
                                                                    "st_app: head = "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    ", eff_head: "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", ty_head = "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    (Pulse_Syntax_Printer.tot_or_ghost_to_string
                                                                    eff_head)))))
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
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___4))
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match 
                                                                    Pulse_Syntax_Pure.is_arrow
                                                                    ty_head
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    b ->
                                                                    Obj.magic
                                                                    (apply_impure_function
                                                                    t1.Pulse_Syntax_Base.range2
                                                                    g01 uvs g
                                                                    ctxt ()
                                                                    post_hint1
                                                                    res_ppname
                                                                    head1
                                                                    qual arg
                                                                    ty_head
                                                                    eff_head
                                                                    () b)
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (117)))))
                                                                    (Obj.magic
                                                                    (norm_typing
                                                                    g head1
                                                                    eff_head
                                                                    ty_head
                                                                    ()
                                                                    [FStar_Pervasives.weak;
                                                                    FStar_Pervasives.hnf;
                                                                    FStar_Pervasives.delta]))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (ty',
                                                                    typing)
                                                                    ->
                                                                    (match 
                                                                    Pulse_Syntax_Pure.is_arrow
                                                                    ty'
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty_head))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (35)))))
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
                                                                    head1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Expected an arrow type; but head "
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    " has type "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    uu___6))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t1.Pulse_Syntax_Base.range2))
                                                                    uu___6))
                                                                    uu___6))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    b ->
                                                                    Obj.magic
                                                                    (apply_impure_function
                                                                    t1.Pulse_Syntax_Base.range2
                                                                    g01 uvs g
                                                                    ctxt ()
                                                                    post_hint1
                                                                    res_ppname
                                                                    head1
                                                                    qual arg
                                                                    ty'
                                                                    eff_head
                                                                    () b)))
                                                                    uu___5)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                          uu___1))) uu___)))
                                uu___))) uu___)