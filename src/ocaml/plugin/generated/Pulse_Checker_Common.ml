open Prims
let (mk_abs :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun t ->
      FStar_Reflection_Typing.mk_abs (Pulse_Elaborate_Pure.elab_term ty)
        FStar_Reflection_V2_Data.Q_Explicit
        (Pulse_Elaborate_Pure.elab_term t)
let (mk_arrow :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun t ->
      FStar_Reflection_Typing.mk_arrow (Pulse_Elaborate_Pure.elab_term ty)
        FStar_Reflection_V2_Data.Q_Explicit
        (Pulse_Elaborate_Pure.elab_term t)
type post_hint_t =
  {
  g: Pulse_Typing_Env.env ;
  ret_ty: Pulse_Syntax_Base.term ;
  u: Pulse_Syntax_Base.universe ;
  ty_typing: unit ;
  post: Pulse_Syntax_Base.term ;
  post_typing: unit }
let (__proj__Mkpost_hint_t__item__g : post_hint_t -> Pulse_Typing_Env.env) =
  fun projectee ->
    match projectee with
    | { g; ret_ty; u; ty_typing; post; post_typing;_} -> g
let (__proj__Mkpost_hint_t__item__ret_ty :
  post_hint_t -> Pulse_Syntax_Base.term) =
  fun projectee ->
    match projectee with
    | { g; ret_ty; u; ty_typing; post; post_typing;_} -> ret_ty
let (__proj__Mkpost_hint_t__item__u :
  post_hint_t -> Pulse_Syntax_Base.universe) =
  fun projectee ->
    match projectee with
    | { g; ret_ty; u; ty_typing; post; post_typing;_} -> u

let (__proj__Mkpost_hint_t__item__post :
  post_hint_t -> Pulse_Syntax_Base.term) =
  fun projectee ->
    match projectee with
    | { g; ret_ty; u; ty_typing; post; post_typing;_} -> post
type ('g, 'p) post_hint_for_env_p = unit
type 'g post_hint_for_env = post_hint_t
type 'g post_hint_opt = post_hint_t FStar_Pervasives_Native.option
type ('g, 'p, 'x) post_hint_typing_t =
  {
  ty_typing1: unit ;
  post_typing1: unit }


let (post_hint_typing :
  Pulse_Typing_Env.env ->
    unit post_hint_for_env ->
      Pulse_Syntax_Base.var -> (unit, unit, unit) post_hint_typing_t)
  = fun g -> fun p -> fun x -> { ty_typing1 = (); post_typing1 = () }
let (intro_post_hint :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term ->
        (unit post_hint_for_env, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ret_ty_opt ->
      fun post ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                   (Prims.of_int (20)) (Prims.of_int (10))
                   (Prims.of_int (20)) (Prims.of_int (17)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                   (Prims.of_int (20)) (Prims.of_int (20))
                   (Prims.of_int (32)) (Prims.of_int (109)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Typing_Env.fresh g))
          (fun uu___ ->
             (fun x ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                              (Prims.of_int (22)) (Prims.of_int (6))
                              (Prims.of_int (24)) (Prims.of_int (19)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                              (Prims.of_int (25)) (Prims.of_int (4))
                              (Prims.of_int (32)) (Prims.of_int (109)))))
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
                                         (Prims.of_int (26))
                                         (Prims.of_int (18))
                                         (Prims.of_int (26))
                                         (Prims.of_int (56)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Common.fst"
                                         (Prims.of_int (25))
                                         (Prims.of_int (4))
                                         (Prims.of_int (32))
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
                                                        (Prims.of_int (27))
                                                        (Prims.of_int (27))
                                                        (Prims.of_int (27))
                                                        (Prims.of_int (53)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Common.fst"
                                                        (Prims.of_int (26))
                                                        (Prims.of_int (59))
                                                        (Prims.of_int (32))
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
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (119)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (32))
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
                                                                    g;
                                                                    ret_ty =
                                                                    ret_ty1;
                                                                    u;
                                                                    ty_typing
                                                                    = ();
                                                                    post =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post1 x);
                                                                    post_typing
                                                                    = ()
                                                                    }))))
                                                    uu___2))) uu___))) uu___)))
               uu___)
let (post_hint_from_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) Pulse_Typing_Metatheory.comp_typing_u ->
        unit post_hint_for_env)
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
                g;
                ret_ty = (Pulse_Syntax_Base.comp_res c);
                u = (Pulse_Syntax_Base.comp_u c);
                ty_typing = ();
                post = (Pulse_Syntax_Base.comp_post c);
                post_typing = ()
              } in
            p
exception Framing_failure of Pulse_Checker_Framing.framing_failure 
let (uu___is_Framing_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Framing_failure uu___ -> true | uu___ -> false
let (__proj__Framing_failure__item__uu___ :
  Prims.exn -> Pulse_Checker_Framing.framing_failure) =
  fun projectee -> match projectee with | Framing_failure uu___ -> uu___
let (try_frame_pre :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              ((Pulse_Syntax_Base.comp_st,
                 (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun c ->
            fun t_typing ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                         (Prims.of_int (55)) (Prims.of_int (12))
                         (Prims.of_int (55)) (Prims.of_int (53)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                         (Prims.of_int (56)) (Prims.of_int (4))
                         (Prims.of_int (64)) (Prims.of_int (48)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Checker_Pure.push_context "try_frame_pre"
                        t.Pulse_Syntax_Base.range2 g))
                (fun uu___ ->
                   (fun g1 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Common.fst"
                                    (Prims.of_int (56)) (Prims.of_int (4))
                                    (Prims.of_int (61)) (Prims.of_int (56)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Common.fst"
                                    (Prims.of_int (62)) (Prims.of_int (4))
                                    (Prims.of_int (64)) (Prims.of_int (48)))))
                           (if
                              Pulse_RuntimeUtils.debug_at_level
                                (Pulse_Typing_Env.fstar_env g1) "try_frame"
                            then
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Common.fst"
                                               (Prims.of_int (57))
                                               (Prims.of_int (17))
                                               (Prims.of_int (61))
                                               (Prims.of_int (56)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Common.fst"
                                               (Prims.of_int (57))
                                               (Prims.of_int (9))
                                               (Prims.of_int (61))
                                               (Prims.of_int (56)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Common.fst"
                                                     (Prims.of_int (61))
                                                     (Prims.of_int (33))
                                                     (Prims.of_int (61))
                                                     (Prims.of_int (55)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Common.fst"
                                                     (Prims.of_int (57))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (61))
                                                     (Prims.of_int (56)))))
                                            (Obj.magic
                                               (Pulse_Syntax_Printer.term_to_string
                                                  pre))
                                            (fun uu___ ->
                                               (fun uu___ ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Common.fst"
                                                                (Prims.of_int (57))
                                                                (Prims.of_int (17))
                                                                (Prims.of_int (61))
                                                                (Prims.of_int (56)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Common.fst"
                                                                (Prims.of_int (57))
                                                                (Prims.of_int (17))
                                                                (Prims.of_int (61))
                                                                (Prims.of_int (56)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (53)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (56)))))
                                                             (Obj.magic
                                                                (Pulse_Syntax_Printer.comp_to_string
                                                                   c))
                                                             (fun uu___1 ->
                                                                (fun uu___1
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Env.print_context
                                                                    g1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (60)))))
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
                                                                    t.Pulse_Syntax_Base.range2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "(Try frame@"
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    ") with "))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\n\tcomp="))
                                                                    (Prims.strcat
                                                                    x1
                                                                    ",\n\tpre="))
                                                                    (Prims.strcat
                                                                    x2 "\n")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
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
                                              (FStar_Tactics_V2_Builtins.print
                                                 uu___)) uu___)))
                            else
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 -> ()))))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Common.fst"
                                               (Prims.of_int (62))
                                               (Prims.of_int (10))
                                               (Prims.of_int (62))
                                               (Prims.of_int (68)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Common.fst"
                                               (Prims.of_int (62))
                                               (Prims.of_int (4))
                                               (Prims.of_int (64))
                                               (Prims.of_int (48)))))
                                      (Obj.magic
                                         (Pulse_Checker_Framing.try_frame_pre
                                            g1 t pre () c t_typing))
                                      (fun uu___1 ->
                                         match uu___1 with
                                         | FStar_Pervasives.Inl ok ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 -> ok)
                                         | FStar_Pervasives.Inr fail ->
                                             FStar_Tactics_Effect.raise
                                               (Framing_failure fail))))
                                uu___))) uu___)
type ('c, 'postuhint) comp_post_matches_hint = Obj.t
type ('g, 'ctxt, 'postuhint) checker_result_t =
  (Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
    (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple3
type check_t =
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit post_hint_opt ->
            ((unit, unit, unit) checker_result_t, unit)
              FStar_Tactics_Effect.tac_repr
let (replace_equiv_post :
  Pulse_Syntax_Base.range ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.comp ->
        (unit, unit) Pulse_Typing_Metatheory.comp_typing_u ->
          unit post_hint_opt ->
            ((Pulse_Syntax_Base.comp,
               (unit, unit, unit) Pulse_Typing.st_equiv) Prims.dtuple2,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun r ->
    fun g ->
      fun c ->
        fun ct ->
          fun post_hint ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                       (Prims.of_int (75)) (Prims.of_int (12))
                       (Prims.of_int (75)) (Prims.of_int (52)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                       (Prims.of_int (75)) (Prims.of_int (55))
                       (Prims.of_int (125)) (Prims.of_int (7)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Pulse_Checker_Pure.push_context "replace_equiv_post" r g))
              (fun uu___ ->
                 (fun g1 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Common.fst"
                                  (Prims.of_int (76)) (Prims.of_int (50))
                                  (Prims.of_int (76)) (Prims.of_int (67)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Common.fst"
                                  (Prims.of_int (75)) (Prims.of_int (55))
                                  (Prims.of_int (125)) (Prims.of_int (7)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> Pulse_Syntax_Base.st_comp_of_comp c))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | { Pulse_Syntax_Base.u = u_c;
                                   Pulse_Syntax_Base.res = res_c;
                                   Pulse_Syntax_Base.pre = pre_c;
                                   Pulse_Syntax_Base.post = post_c;_} ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Common.fst"
                                                 (Prims.of_int (77))
                                                 (Prims.of_int (20))
                                                 (Prims.of_int (77))
                                                 (Prims.of_int (55)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Common.fst"
                                                 (Prims.of_int (77))
                                                 (Prims.of_int (58))
                                                 (Prims.of_int (125))
                                                 (Prims.of_int (7)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              Pulse_Typing_Metatheory.comp_typing_inversion
                                                g c ct))
                                        (fun uu___1 ->
                                           (fun st_typing ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Common.fst"
                                                            (Prims.of_int (78))
                                                            (Prims.of_int (61))
                                                            (Prims.of_int (78))
                                                            (Prims.of_int (106)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Common.fst"
                                                            (Prims.of_int (77))
                                                            (Prims.of_int (58))
                                                            (Prims.of_int (125))
                                                            (Prims.of_int (7)))))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                           g
                                                           (Pulse_Syntax_Base.st_comp_of_comp
                                                              c) st_typing))
                                                   (fun uu___1 ->
                                                      (fun uu___1 ->
                                                         match uu___1 with
                                                         | FStar_Pervasives.Mkdtuple4
                                                             (res_c_typing,
                                                              pre_c_typing,
                                                              x,
                                                              post_c_typing)
                                                             ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (22)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (7)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.v_as_nv
                                                                    x))
                                                                  (fun uu___2
                                                                    ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px) res_c))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    g_post ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post_c px))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    post_c_opened
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
                                                                    uu___2 ->
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    (Pulse_Typing.ST_VPropEquiv
                                                                    (g1, c,
                                                                    c, x, (),
                                                                    (), (),
                                                                    (), ()))))))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    Prims.op_Negation
                                                                    ((Pulse_Syntax_Base.eq_univ
                                                                    u_c
                                                                    post.u)
                                                                    &&
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    res_c
                                                                    post.ret_ty))
                                                                    then
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    res_c))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    post.ret_ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (39)))))
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
                                                                    r))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "("
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    ") Inferred result type does not match annotation.\nExpected type "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    "\nGot type "))
                                                                    (Prims.strcat
                                                                    x2 "\n")))))
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
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___2))
                                                                    uu___2)
                                                                    else
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    post.post)
                                                                    then
                                                                    Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Unexpected variable clash with annotated postcondition"
                                                                    else
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post.post
                                                                    px))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Common.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Framing.check_vprop_equiv
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "check_vprop_equiv"
                                                                    r g_post)
                                                                    post_c_opened
                                                                    post_opened
                                                                    ()))
                                                                    (fun
                                                                    post_c_post_eq
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.with_st_comp
                                                                    c
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u_c;
                                                                    Pulse_Syntax_Base.res
                                                                    = res_c;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre_c;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x)
                                                                    }),
                                                                    (Pulse_Typing.ST_VPropEquiv
                                                                    (g1, c,
                                                                    (Pulse_Syntax_Base.with_st_comp
                                                                    c
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u_c;
                                                                    Pulse_Syntax_Base.res
                                                                    = res_c;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre_c;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x)
                                                                    }), x,
                                                                    (), (),
                                                                    (), (),
                                                                    ())))))))
                                                                    uu___4))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                        uu___1))) uu___1)))
                              uu___))) uu___)
let (repack :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        (Pulse_Syntax_Base.comp_st,
          (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2 ->
          unit post_hint_opt ->
            ((unit, unit, unit) checker_result_t, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun t ->
        fun x ->
          fun post_hint ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                       (Prims.of_int (132)) (Prims.of_int (23))
                       (Prims.of_int (132)) (Prims.of_int (24)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                       (Prims.of_int (132)) (Prims.of_int (3))
                       (Prims.of_int (139)) (Prims.of_int (24)))))
              (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | Prims.Mkdtuple2 (c, d_c) ->
                        if Pulse_Syntax_Base.stateful_comp c
                        then
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Common.fst"
                                           (Prims.of_int (136))
                                           (Prims.of_int (30))
                                           (Prims.of_int (136))
                                           (Prims.of_int (109)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Common.fst"
                                           (Prims.of_int (135))
                                           (Prims.of_int (32))
                                           (Prims.of_int (137))
                                           (Prims.of_int (46)))))
                                  (Obj.magic
                                     (replace_equiv_post
                                        t.Pulse_Syntax_Base.range2 g c
                                        (Pulse_Typing_Metatheory.st_typing_correctness
                                           g t c d_c) post_hint))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          match uu___1 with
                                          | Prims.Mkdtuple2 (c1, c_c1_eq) ->
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
                                     FStar_Pervasives.Mkdtuple3 (t, c, d_c)))))
                   uu___)
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
                         (Prims.of_int (153)) (Prims.of_int (8))
                         (Prims.of_int (153)) (Prims.of_int (52)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                         (Prims.of_int (155)) (Prims.of_int (4))
                         (Prims.of_int (170)) (Prims.of_int (44)))))
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
                                        (Prims.of_int (157))
                                        (Prims.of_int (16))
                                        (Prims.of_int (157))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Common.fst"
                                        (Prims.of_int (158))
                                        (Prims.of_int (6))
                                        (Prims.of_int (158))
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
                                        (Prims.of_int (160))
                                        (Prims.of_int (16))
                                        (Prims.of_int (160))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Common.fst"
                                        (Prims.of_int (160))
                                        (Prims.of_int (42))
                                        (Prims.of_int (164))
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
                                                   (Prims.of_int (161))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (161))
                                                   (Prims.of_int (53)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Common.fst"
                                                   (Prims.of_int (160))
                                                   (Prims.of_int (42))
                                                   (Prims.of_int (164))
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
                                        (Prims.of_int (166))
                                        (Prims.of_int (16))
                                        (Prims.of_int (166))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Common.fst"
                                        (Prims.of_int (166))
                                        (Prims.of_int (42))
                                        (Prims.of_int (170))
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
                                                   (Prims.of_int (167))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (167))
                                                   (Prims.of_int (53)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Common.fst"
                                                   (Prims.of_int (166))
                                                   (Prims.of_int (42))
                                                   (Prims.of_int (170))
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