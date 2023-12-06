open Prims
exception Extraction_failure of Prims.string 
let (uu___is_Extraction_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Extraction_failure uu___ -> true | uu___ -> false
let (__proj__Extraction_failure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | Extraction_failure uu___ -> uu___
type env =
  {
  uenv_inner: Pulse_Extract_CompilerLib.uenv ;
  coreenv: Pulse_Typing_Env.env }
let (__proj__Mkenv__item__uenv_inner : env -> Pulse_Extract_CompilerLib.uenv)
  =
  fun projectee ->
    match projectee with | { uenv_inner; coreenv;_} -> uenv_inner
let (__proj__Mkenv__item__coreenv : env -> Pulse_Typing_Env.env) =
  fun projectee -> match projectee with | { uenv_inner; coreenv;_} -> coreenv
type name = (Pulse_Syntax_Base.ppname * Prims.nat)
let (topenv_of_env : env -> FStar_Reflection_Typing.fstar_top_env) =
  fun g -> Pulse_Typing_Env.fstar_env g.coreenv
let (tcenv_of_env : env -> FStar_Reflection_Types.env) =
  fun g -> Pulse_Typing.elab_env g.coreenv
let (uenv_of_env : env -> Pulse_Extract_CompilerLib.uenv) =
  fun g -> Pulse_Extract_CompilerLib.set_tcenv g.uenv_inner (tcenv_of_env g)
let (debug :
  env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun f ->
           if
             Pulse_RuntimeUtils.debug_at_level
               (Pulse_Typing_Env.fstar_env g.coreenv) "pulse_extraction"
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (37)) (Prims.of_int (17))
                              (Prims.of_int (37)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (37)) (Prims.of_int (9))
                              (Prims.of_int (37)) (Prims.of_int (22)))))
                     (Obj.magic (f ()))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___))
                          uu___)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let (term_as_mlexpr :
  env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Extract_CompilerLib.mlexpr, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   match Pulse_Extract_CompilerLib.term_as_mlexpr
                           (uenv_of_env g)
                           (Pulse_Extract_CompilerLib.normalize_for_extraction
                              (uenv_of_env g)
                              (Pulse_Elaborate_Pure.elab_term t))
                   with
                   | (mlt, uu___1, uu___2) -> mlt))) uu___1 uu___
let (term_as_mlty :
  env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Extract_CompilerLib.mlty, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   Pulse_Extract_CompilerLib.term_as_mlty (uenv_of_env g)
                     (Pulse_Elaborate_Pure.elab_term t)))) uu___1 uu___
let (extend_env :
  env ->
    Pulse_Syntax_Base.binder ->
      ((env * Pulse_Extract_CompilerLib.mlident *
         Pulse_Extract_CompilerLib.mlty * name),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (55)) (Prims.of_int (15)) (Prims.of_int (55))
                 (Prims.of_int (41)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (55)) (Prims.of_int (44)) (Prims.of_int (62))
                 (Prims.of_int (64)))))
        (Obj.magic (term_as_mlty g b.Pulse_Syntax_Base.binder_ty))
        (fun uu___ ->
           (fun mlty ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (56)) (Prims.of_int (12))
                            (Prims.of_int (56)) (Prims.of_int (29)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (56)) (Prims.of_int (32))
                            (Prims.of_int (62)) (Prims.of_int (64)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Typing_Env.fresh g.coreenv))
                   (fun uu___ ->
                      (fun x ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (57))
                                       (Prims.of_int (18))
                                       (Prims.of_int (57))
                                       (Prims.of_int (72)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (58)) (Prims.of_int (4))
                                       (Prims.of_int (62))
                                       (Prims.of_int (64)))))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ ->
                                    Pulse_Typing_Env.push_binding g.coreenv x
                                      b.Pulse_Syntax_Base.binder_ppname
                                      b.Pulse_Syntax_Base.binder_ty))
                              (fun uu___ ->
                                 (fun coreenv ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (58))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (67)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (68))
                                                  (Prims.of_int (62))
                                                  (Prims.of_int (64)))))
                                         (Obj.magic
                                            (debug g
                                               (fun uu___ ->
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (60))
                                                             (Prims.of_int (38))
                                                             (Prims.of_int (60))
                                                             (Prims.of_int (66)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (58))
                                                             (Prims.of_int (22))
                                                             (Prims.of_int (60))
                                                             (Prims.of_int (66)))))
                                                    (Obj.magic
                                                       (Pulse_Syntax_Printer.term_to_string
                                                          b.Pulse_Syntax_Base.binder_ty))
                                                    (fun uu___1 ->
                                                       (fun uu___1 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (66)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (66)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.binder_to_string
                                                                    b))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Extending environment with "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " : "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                               (fun uu___2 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                         uu___1))))
                                         (fun uu___ ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 match Pulse_Extract_CompilerLib.extend_bv
                                                         g.uenv_inner
                                                         b.Pulse_Syntax_Base.binder_ppname
                                                         x mlty
                                                 with
                                                 | (uenv_inner, mlident) ->
                                                     ({ uenv_inner; coreenv },
                                                       mlident, mlty,
                                                       ((b.Pulse_Syntax_Base.binder_ppname),
                                                         x)))))) uu___)))
                        uu___))) uu___)
let rec (name_as_mlpath :
  FStar_Reflection_Types.name ->
    (Pulse_Extract_CompilerLib.mlpath, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun x ->
       match x with
       | [] ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_V2_Derived.fail "Unexpected empty name"))
       | x1::[] ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ([], x1))))
       | x1::xs ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (70)) (Prims.of_int (18))
                            (Prims.of_int (70)) (Prims.of_int (35)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (69)) (Prims.of_int (16))
                            (Prims.of_int (71)) (Prims.of_int (16)))))
                   (Obj.magic (name_as_mlpath xs))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           match uu___ with | (xs1, x2) -> ((x2 :: xs1), x2))))))
      uu___
let (extract_constant :
  env ->
    FStar_Reflection_V2_Data.vconst ->
      (Pulse_Extract_CompilerLib.mlconstant, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (76)) (Prims.of_int (12)) (Prims.of_int (76))
                 (Prims.of_int (36)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (76)) (Prims.of_int (39)) (Prims.of_int (80))
                 (Prims.of_int (17)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_Const c)))
        (fun uu___ ->
           (fun e ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (77)) (Prims.of_int (20))
                            (Prims.of_int (77)) (Prims.of_int (64)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (76)) (Prims.of_int (39))
                            (Prims.of_int (80)) (Prims.of_int (17)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         Pulse_Extract_CompilerLib.term_as_mlexpr
                           (uenv_of_env g) e))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | (mle, uu___1, uu___2) ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (78))
                                           (Prims.of_int (10))
                                           (Prims.of_int (78))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (78))
                                           (Prims.of_int (4))
                                           (Prims.of_int (80))
                                           (Prims.of_int (17)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 ->
                                        Pulse_Extract_CompilerLib.mlconstant_of_mlexpr
                                          mle))
                                  (fun uu___3 ->
                                     match uu___3 with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Tactics_Effect.raise
                                           (Extraction_failure
                                              "Failed to extract constant")
                                     | FStar_Pervasives_Native.Some c1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> c1)))) uu___)))
             uu___)
let rec (extend_env_pat_core :
  env ->
    Pulse_Syntax_Base.pattern ->
      ((env * Pulse_Extract_CompilerLib.mlpattern Prims.list *
         Pulse_Typing_Env.binding Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun p ->
           match p with
           | Pulse_Syntax_Base.Pat_Dot_Term uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> (g, [], []))))
           | Pulse_Syntax_Base.Pat_Var (pp, sort) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (87)) (Prims.of_int (14))
                                (Prims.of_int (87)) (Prims.of_int (31)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (87)) (Prims.of_int (34))
                                (Prims.of_int (97)) (Prims.of_int (25)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ -> Pulse_Typing_Env.fresh g.coreenv))
                       (fun uu___ ->
                          (fun x ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (88))
                                           (Prims.of_int (15))
                                           (Prims.of_int (88))
                                           (Prims.of_int (47)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (88))
                                           (Prims.of_int (50))
                                           (Prims.of_int (97))
                                           (Prims.of_int (25)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ ->
                                        Pulse_Syntax_Base.mk_ppname pp
                                          FStar_Range.range_0))
                                  (fun uu___ ->
                                     (fun pp1 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (89))
                                                      (Prims.of_int (15))
                                                      (Prims.of_int (89))
                                                      (Prims.of_int (28)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (90))
                                                      (Prims.of_int (33))
                                                      (Prims.of_int (97))
                                                      (Prims.of_int (25)))))
                                             (Obj.magic
                                                (FStar_Tactics_Unseal.unseal
                                                   sort))
                                             (fun uu___ ->
                                                (fun ty ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (91))
                                                                 (Prims.of_int (15))
                                                                 (Prims.of_int (91))
                                                                 (Prims.of_int (47)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (92))
                                                                 (Prims.of_int (6))
                                                                 (Prims.of_int (97))
                                                                 (Prims.of_int (25)))))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___ ->
                                                              Pulse_Syntax_Base.tm_fstar
                                                                ty
                                                                (FStar_Reflection_V2_Builtins.range_of_term
                                                                   ty)))
                                                        (fun uu___ ->
                                                           (fun ty1 ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (106)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (25)))))
                                                                   (Obj.magic
                                                                    (debug g
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Unseal.unseal
                                                                    pp1.Pulse_Syntax_Base.name))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Pushing pat_var "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " : "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                                    uu___1))))
                                                                   (fun uu___
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    match 
                                                                    Pulse_Extract_CompilerLib.extend_bv
                                                                    g.uenv_inner
                                                                    pp1 x
                                                                    Pulse_Extract_CompilerLib.mlty_top
                                                                    with
                                                                    | 
                                                                    (uenv_inner,
                                                                    mlident)
                                                                    ->
                                                                    ({
                                                                    uenv_inner;
                                                                    coreenv =
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g.coreenv
                                                                    x pp1 ty1)
                                                                    },
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mlp_var
                                                                    mlident],
                                                                    [
                                                                    (x,
                                                                    Pulse_Syntax_Base.tm_unknown)])))))
                                                             uu___))) uu___)))
                                       uu___))) uu___)))
           | Pulse_Syntax_Base.Pat_Cons (f, pats) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (101)) (Prims.of_int (8))
                                (Prims.of_int (106)) (Prims.of_int (14)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (99)) (Prims.of_int (24))
                                (Prims.of_int (108)) (Prims.of_int (68)))))
                       (Obj.magic
                          (FStar_Tactics_Util.fold_left
                             (fun uu___ ->
                                fun uu___1 ->
                                  match (uu___, uu___1) with
                                  | ((g1, pats1, bindings), (p1, uu___2)) ->
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (103))
                                                 (Prims.of_int (38))
                                                 (Prims.of_int (103))
                                                 (Prims.of_int (61)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (102))
                                                 (Prims.of_int (44))
                                                 (Prims.of_int (104))
                                                 (Prims.of_int (47)))))
                                        (Obj.magic
                                           (extend_env_pat_core g1 p1))
                                        (fun uu___3 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___4 ->
                                                match uu___3 with
                                                | (g2, pats', bindings') ->
                                                    (g2,
                                                      (FStar_List_Tot_Base.op_At
                                                         pats1 pats'),
                                                      (FStar_List_Tot_Base.op_At
                                                         bindings bindings')))))
                             (g, [], []) pats))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | (g1, pats1, bindings) ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (108))
                                               (Prims.of_int (9))
                                               (Prims.of_int (108))
                                               (Prims.of_int (58)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (108))
                                               (Prims.of_int (6))
                                               (Prims.of_int (108))
                                               (Prims.of_int (68)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (108))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (108))
                                                     (Prims.of_int (57)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (108))
                                                     (Prims.of_int (9))
                                                     (Prims.of_int (108))
                                                     (Prims.of_int (58)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Extract.Main.fst"
                                                           (Prims.of_int (108))
                                                           (Prims.of_int (26))
                                                           (Prims.of_int (108))
                                                           (Prims.of_int (52)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Extract.Main.fst"
                                                           (Prims.of_int (108))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (108))
                                                           (Prims.of_int (57)))))
                                                  (Obj.magic
                                                     (name_as_mlpath
                                                        f.Pulse_Syntax_Base.fv_name))
                                                  (fun uu___1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          Pulse_Extract_CompilerLib.mlp_constructor
                                                            uu___1 pats1))))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 -> [uu___1]))))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              (g1, uu___1, bindings)))))
                            uu___)))
           | Pulse_Syntax_Base.Pat_Constant c ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (110)) (Prims.of_int (14))
                                (Prims.of_int (110)) (Prims.of_int (34)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (111)) (Prims.of_int (6))
                                (Prims.of_int (111)) (Prims.of_int (26)))))
                       (Obj.magic (extract_constant g c))
                       (fun c1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               (g, [Pulse_Extract_CompilerLib.mlp_const c1],
                                 [])))))) uu___1 uu___
let (extend_env_pat :
  env ->
    Pulse_Syntax_Base.pattern ->
      ((env * Pulse_Extract_CompilerLib.mlpattern * Pulse_Typing_Env.binding
         Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (113)) (Prims.of_int (20))
                 (Prims.of_int (113)) (Prims.of_int (43)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (112)) (Prims.of_int (24))
                 (Prims.of_int (116)) (Prims.of_int (72)))))
        (Obj.magic (extend_env_pat_core g p))
        (fun uu___ ->
           match uu___ with
           | (g1, pats, bs) ->
               (match pats with
                | p1::[] ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 -> (g1, p1, bs))
                | uu___1 ->
                    FStar_Tactics_Effect.raise
                      (Extraction_failure "Unexpected extraction of pattern")))
let (unit_val : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Base.tm_fstar Pulse_Reflection_Util.unit_tm
    FStar_Range.range_0
let (is_erasable :
  Pulse_Syntax_Base.st_term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (120)) (Prims.of_int (12)) (Prims.of_int (120))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (121)) (Prims.of_int (2)) (Prims.of_int (123))
               (Prims.of_int (14)))))
      (Obj.magic (FStar_Tactics_Unseal.unseal p.Pulse_Syntax_Base.effect_tag))
      (fun tag ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              match tag with
              | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.STT_Ghost) ->
                  true
              | uu___1 -> false))
let (head_and_args :
  Pulse_Syntax_Base.term ->
    (FStar_Reflection_Types.term * FStar_Reflection_V2_Data.argv Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match t.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_FStar t0 ->
        FStar_Pervasives_Native.Some
          (FStar_Reflection_V2_Derived.collect_app_ln t0)
    | uu___ -> FStar_Pervasives_Native.None
let (term_eq_string :
  Prims.string -> FStar_Reflection_Types.term -> Prims.bool) =
  fun s ->
    fun t ->
      match FStar_Reflection_V2_Builtins.inspect_ln t with
      | FStar_Reflection_V2_Data.Tv_Const (FStar_Reflection_V2_Data.C_String
          s') -> s = s'
      | uu___ -> false
let (maybe_unfold_head :
  env ->
    FStar_Reflection_Types.term ->
      ((Pulse_Syntax_Base.st_term, FStar_Reflection_Types.term)
         FStar_Pervasives.either FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun head ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (138)) (Prims.of_int (4)) (Prims.of_int (138))
                 (Prims.of_int (89)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (139)) (Prims.of_int (4)) (Prims.of_int (165))
                 (Prims.of_int (15)))))
        (Obj.magic
           (debug g
              (fun uu___ ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (138)) (Prims.of_int (65))
                            (Prims.of_int (138)) (Prims.of_int (88)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string head))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "Maybe unfolding head "
                             (Prims.strcat uu___1 "\n"))))))
        (fun uu___ ->
           (fun uu___ ->
              match FStar_Reflection_V2_Builtins.inspect_ln head with
              | FStar_Reflection_V2_Data.Tv_FVar f ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Extract.Main.fst"
                                   (Prims.of_int (141)) (Prims.of_int (17))
                                   (Prims.of_int (141)) (Prims.of_int (31)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Extract.Main.fst"
                                   (Prims.of_int (142)) (Prims.of_int (6))
                                   (Prims.of_int (160)) (Prims.of_int (17)))))
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 ->
                                FStar_Reflection_V2_Builtins.inspect_fv f))
                          (fun uu___1 ->
                             (fun name1 ->
                                match FStar_Reflection_V2_Builtins.lookup_typ
                                        (topenv_of_env g) name1
                                with
                                | FStar_Pervasives_Native.None ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___1 ->
                                               FStar_Pervasives_Native.None)))
                                | FStar_Pervasives_Native.Some se ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (145))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (145))
                                                     (Prims.of_int (37)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (145))
                                                     (Prims.of_int (40))
                                                     (Prims.of_int (160))
                                                     (Prims.of_int (17)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  FStar_Reflection_V2_Builtins.sigelt_attrs
                                                    se))
                                            (fun uu___1 ->
                                               (fun attrs ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (146))
                                                                (Prims.of_int (20))
                                                                (Prims.of_int (146))
                                                                (Prims.of_int (37)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (147))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (160))
                                                                (Prims.of_int (17)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___1 ->
                                                             FStar_Reflection_V2_Builtins.sigelt_quals
                                                               se))
                                                       (fun uu___1 ->
                                                          (fun quals ->
                                                             if
                                                               (FStar_List_Tot_Base.existsb
                                                                  (term_eq_string
                                                                    "inline")
                                                                  attrs)
                                                                 ||
                                                                 (FStar_List_Tot_Base.existsb
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Data.Inline_for_extraction
                                                                    -> true
                                                                    | 
                                                                    uu___2 ->
                                                                    false)
                                                                    quals)
                                                             then
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    match 
                                                                    Pulse_Extract_CompilerLib.sigelt_extension_data
                                                                    se
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (debug g
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    head))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Unfolded head "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (debug g
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    se1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "to "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Inl
                                                                    se1)))))
                                                                    uu___1)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_NamedView.inspect_sigelt
                                                                    se))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Sg_Let
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    =
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    = uu___3;
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = [];
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = uu___4;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    = lb_def;_}::[];_}
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Inr
                                                                    lb_def)
                                                                    | 
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.None))))
                                                             else
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives_Native.None))))
                                                            uu___1))) uu___1))))
                               uu___1)))
              | FStar_Reflection_V2_Data.Tv_UInst (f, uu___1) ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> FStar_Pervasives_Native.None)))
              | uu___1 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> FStar_Pervasives_Native.None))))
             uu___)
let rec (st_term_abs_take_n_args :
  Prims.nat ->
    Pulse_Syntax_Base.st_term -> (Pulse_Syntax_Base.st_term * Prims.nat))
  =
  fun n_args ->
    fun t ->
      if n_args = Prims.int_zero
      then (t, Prims.int_zero)
      else
        (match t.Pulse_Syntax_Base.term1 with
         | Pulse_Syntax_Base.Tm_Abs
             { Pulse_Syntax_Base.b = uu___1; Pulse_Syntax_Base.q = uu___2;
               Pulse_Syntax_Base.ascription = uu___3;
               Pulse_Syntax_Base.body = body;_}
             -> st_term_abs_take_n_args (n_args - Prims.int_one) body
         | uu___1 -> (t, n_args))
let rec (term_abs_take_n_args :
  Prims.nat ->
    FStar_Reflection_Types.term -> (FStar_Reflection_Types.term * Prims.nat))
  =
  fun n_args ->
    fun t ->
      if n_args = Prims.int_zero
      then (t, Prims.int_zero)
      else
        (match FStar_Reflection_V2_Builtins.inspect_ln t with
         | FStar_Reflection_V2_Data.Tv_Abs (uu___1, body) ->
             term_abs_take_n_args (n_args - Prims.int_one) body
         | uu___1 -> (t, n_args))
let (abs_take_n_args :
  Prims.nat ->
    (Pulse_Syntax_Base.st_term, FStar_Reflection_Types.term)
      FStar_Pervasives.either ->
      (((Pulse_Syntax_Base.st_term, FStar_Reflection_Types.term)
         FStar_Pervasives.either * Prims.nat),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun n_args ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   match t with
                   | FStar_Pervasives.Inl t1 ->
                       (match st_term_abs_take_n_args n_args t1 with
                        | (t2, n_args1) ->
                            ((FStar_Pervasives.Inl t2), n_args1))
                   | FStar_Pervasives.Inr t1 ->
                       (match term_abs_take_n_args n_args t1 with
                        | (t2, n_args1) ->
                            ((FStar_Pervasives.Inr t2), n_args1))))) uu___1
        uu___
let rec (unascribe :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match FStar_Reflection_V2_Builtins.inspect_ln t with
       | FStar_Reflection_V2_Data.Tv_AscribedT (e, uu___, uu___1, uu___2) ->
           Obj.magic (Obj.repr (unascribe e))
       | FStar_Reflection_V2_Data.Tv_AscribedC (e, uu___, uu___1, uu___2) ->
           Obj.magic (Obj.repr (unascribe e))
       | uu___ ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> t))))
      uu___
let (maybe_inline :
  env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.st_term FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun head ->
      fun arg ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (202)) (Prims.of_int (2))
                   (Prims.of_int (203)) (Prims.of_int (44)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (204)) (Prims.of_int (2))
                   (Prims.of_int (290)) (Prims.of_int (46)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (203)) (Prims.of_int (22))
                              (Prims.of_int (203)) (Prims.of_int (43)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))))
                     (Obj.magic (Pulse_Syntax_Printer.term_to_string head))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             Prims.strcat "Considering inlining "
                               (Prims.strcat uu___1 "\n"))))))
          (fun uu___ ->
             (fun uu___ ->
                match head_and_args head with
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> FStar_Pervasives_Native.None)))
                | FStar_Pervasives_Native.Some (head1, args) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Extract.Main.fst"
                                     (Prims.of_int (207)) (Prims.of_int (4))
                                     (Prims.of_int (209)) (Prims.of_int (41)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Extract.Main.fst"
                                     (Prims.of_int (210)) (Prims.of_int (4))
                                     (Prims.of_int (290)) (Prims.of_int (46)))))
                            (Obj.magic
                               (debug g
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (207))
                                                (Prims.of_int (22))
                                                (Prims.of_int (209))
                                                (Prims.of_int (40)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (207))
                                                (Prims.of_int (22))
                                                (Prims.of_int (209))
                                                (Prims.of_int (40)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (208))
                                                      (Prims.of_int (22))
                                                      (Prims.of_int (208))
                                                      (Prims.of_int (45)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Printf.fst"
                                                      (Prims.of_int (121))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (123))
                                                      (Prims.of_int (44)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Builtins.term_to_string
                                                   head1))
                                             (fun uu___2 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___3 ->
                                                     fun x ->
                                                       Prims.strcat
                                                         (Prims.strcat
                                                            "head="
                                                            (Prims.strcat
                                                               uu___2
                                                               " with "))
                                                         (Prims.strcat
                                                            (Prims.string_of_int
                                                               x) " args\n")))))
                                       (fun uu___2 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___3 ->
                                               uu___2
                                                 (FStar_List_Tot_Base.length
                                                    args))))))
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (210))
                                                (Prims.of_int (10))
                                                (Prims.of_int (210))
                                                (Prims.of_int (34)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (210))
                                                (Prims.of_int (4))
                                                (Prims.of_int (290))
                                                (Prims.of_int (46)))))
                                       (Obj.magic (maybe_unfold_head g head1))
                                       (fun uu___2 ->
                                          (fun uu___2 ->
                                             match uu___2 with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (212))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (213))
                                                               (Prims.of_int (52)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (214))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (214))
                                                               (Prims.of_int (10)))))
                                                      (Obj.magic
                                                         (debug g
                                                            (fun uu___3 ->
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (51)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_V2_Builtins.term_to_string
                                                                    head1))
                                                                 (fun uu___4
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "No unfolding of "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    "\n"))))))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              FStar_Pervasives_Native.None)))
                                             | FStar_Pervasives_Native.Some
                                                 def ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (220))
                                                               (Prims.of_int (31))
                                                               (Prims.of_int (220))
                                                               (Prims.of_int (82)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (220))
                                                               (Prims.of_int (85))
                                                               (Prims.of_int (290))
                                                               (Prims.of_int (46)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            fun a ->
                                                              Pulse_Syntax_Base.tm_fstar
                                                                a
                                                                FStar_Range.range_0))
                                                      (fun uu___3 ->
                                                         (fun as_term ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (21)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (46)))))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (t, q) ->
                                                                    ((as_term
                                                                    t),
                                                                    (if
                                                                    FStar_Reflection_V2_Data.uu___is_Q_Implicit
                                                                    q
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit
                                                                    else
                                                                    FStar_Pervasives_Native.None)))
                                                                    args)
                                                                    [
                                                                    (arg,
                                                                    FStar_Pervasives_Native.None)]))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    all_args
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_List_Tot_Base.length
                                                                    all_args))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    n_args ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (abs_take_n_args
                                                                    n_args
                                                                    def))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (body,
                                                                    remaining_args)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.splitAt
                                                                    (n_args -
                                                                    remaining_args)
                                                                    all_args))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (args1,
                                                                    rest) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_List_Tot_Base.fold_right
                                                                    (fun arg1
                                                                    ->
                                                                    fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (i,
                                                                    subst) ->
                                                                    ((i +
                                                                    Prims.int_one),
                                                                    ((Pulse_Syntax_Naming.DT
                                                                    (i,
                                                                    (FStar_Pervasives_Native.fst
                                                                    arg1)))
                                                                    ::
                                                                    subst)))
                                                                    args1
                                                                    (Prims.int_zero,
                                                                    [])))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (uu___6,
                                                                    subst) ->
                                                                    (match body
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body1
                                                                    subst))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    applied_body
                                                                    ->
                                                                    match rest
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    applied_body)))
                                                                    | 
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (79)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun x ->
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    (FStar_Pervasives_Native.fst
                                                                    x)) rest))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_String.concat
                                                                    ", "
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (251))
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
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    head1))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Partial or over application of inlined Pulse definition is not yet supported\n"
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    " has "))
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    x)
                                                                    " arguments, but "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    " were left unapplied")))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    (FStar_List_Tot_Base.length
                                                                    args1)))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    uu___8))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    uu___8))))
                                                                    uu___7))
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (unascribe
                                                                    (Pulse_Syntax_Naming.subst_host_term
                                                                    body1
                                                                    subst)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    applied_body
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun head2
                                                                    ->
                                                                    fun arg1
                                                                    ->
                                                                    fun
                                                                    arg_qual
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    =
                                                                    (Pulse_Syntax_Base.tm_fstar
                                                                    head2
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    head2));
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    =
                                                                    arg_qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    FStar_Range.range_0;
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    Pulse_Syntax_Base.default_effect_hint
                                                                    }))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    mk_st_app
                                                                    ->
                                                                    match rest
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    FStar_Reflection_V2_Builtins.inspect_ln
                                                                    applied_body
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Data.Tv_App
                                                                    (head2,
                                                                    (arg1,
                                                                    aqual))
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    mk_st_app
                                                                    head2
                                                                    (Pulse_Syntax_Base.tm_fstar
                                                                    arg1
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    arg1))
                                                                    (if
                                                                    FStar_Reflection_V2_Data.uu___is_Q_Implicit
                                                                    aqual
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit
                                                                    else
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    uu___7 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    applied_body))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Cannot inline F* definitions of stt terms whose body is not an application; got "
                                                                    (Prims.strcat
                                                                    uu___8 "")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    uu___8))))
                                                                    | 
                                                                    rest1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match 
                                                                    FStar_List_Tot_Base.splitAt
                                                                    ((FStar_List_Tot_Base.length
                                                                    rest1) -
                                                                    Prims.int_one)
                                                                    rest1
                                                                    with
                                                                    | 
                                                                    (rest2,
                                                                    last::[])
                                                                    ->
                                                                    mk_st_app
                                                                    (FStar_List_Tot_Base.fold_left
                                                                    (fun
                                                                    head2 ->
                                                                    fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (tm,
                                                                    qual) ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    (head2,
                                                                    ((Pulse_Elaborate_Pure.elab_term
                                                                    tm),
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    qual
                                                                    then
                                                                    FStar_Reflection_V2_Data.Q_Implicit
                                                                    else
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))))
                                                                    applied_body
                                                                    rest2)
                                                                    (FStar_Pervasives_Native.fst
                                                                    last)
                                                                    (FStar_Pervasives_Native.snd
                                                                    last)))))
                                                                    uu___7)))
                                                                    uu___7))))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                           uu___3))) uu___2)))
                                 uu___1)))) uu___)
let (fresh : env -> Pulse_Syntax_Base.var) =
  fun g -> Pulse_Typing_Env.fresh g.coreenv
let (push_binding :
  env -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.binder -> env) =
  fun g ->
    fun x ->
      fun b ->
        {
          uenv_inner = (g.uenv_inner);
          coreenv =
            (Pulse_Typing_Env.push_binding g.coreenv x
               b.Pulse_Syntax_Base.binder_ppname
               b.Pulse_Syntax_Base.binder_ty)
        }
let (with_open :
  env ->
    Pulse_Syntax_Base.binder ->
      Pulse_Syntax_Base.st_term ->
        (env ->
           Pulse_Syntax_Base.st_term ->
             (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
          -> (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      fun e ->
        fun f ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (299)) (Prims.of_int (10))
                     (Prims.of_int (299)) (Prims.of_int (17)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (299)) (Prims.of_int (20))
                     (Prims.of_int (302)) (Prims.of_int (22)))))
            (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> fresh g))
            (fun uu___ ->
               (fun x ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (300)) (Prims.of_int (10))
                                (Prims.of_int (300)) (Prims.of_int (82)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (300)) (Prims.of_int (85))
                                (Prims.of_int (302)) (Prims.of_int (22)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             Pulse_Syntax_Naming.open_st_term' e
                               (Pulse_Syntax_Pure.tm_var
                                  {
                                    Pulse_Syntax_Base.nm_index = x;
                                    Pulse_Syntax_Base.nm_ppname =
                                      (b.Pulse_Syntax_Base.binder_ppname)
                                  }) Prims.int_zero))
                       (fun uu___ ->
                          (fun e1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (301))
                                           (Prims.of_int (10))
                                           (Prims.of_int (301))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (302))
                                           (Prims.of_int (2))
                                           (Prims.of_int (302))
                                           (Prims.of_int (22)))))
                                  (Obj.magic (f (push_binding g x b) e1))
                                  (fun e2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          Pulse_Syntax_Naming.close_st_term'
                                            e2 x Prims.int_zero)))) uu___)))
                 uu___)
let (is_internal_binder :
  Pulse_Syntax_Base.binder ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (306)) (Prims.of_int (10)) (Prims.of_int (306))
               (Prims.of_int (39)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (307)) (Prims.of_int (2)) (Prims.of_int (311))
               (Prims.of_int (14)))))
      (Obj.magic
         (FStar_Tactics_Unseal.unseal
            (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name))
      (fun s ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              ((((s = "_fret") || (s = "_bind_c")) || (s = "_while_c")) ||
                 (s = "_tbind_c"))
                || (s = "_if_br")))
let (is_return :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun e ->
    match e.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Return
        { Pulse_Syntax_Base.ctag = uu___;
          Pulse_Syntax_Base.insert_eq = uu___1;
          Pulse_Syntax_Base.term = term;_}
        -> FStar_Pervasives_Native.Some term
    | uu___ -> FStar_Pervasives_Native.None
let (is_return_bv0 : Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun e ->
    match is_return e with
    | FStar_Pervasives_Native.Some term ->
        (Pulse_Syntax_Pure.is_bvar term) =
          (FStar_Pervasives_Native.Some Prims.int_zero)
    | uu___ -> false
let (simplify_nested_let :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.binder ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.st_term FStar_Pervasives_Native.option)
  =
  fun e ->
    fun b_x ->
      fun head ->
        fun e3 ->
          let mk t =
            {
              Pulse_Syntax_Base.term1 = t;
              Pulse_Syntax_Base.range2 = (e.Pulse_Syntax_Base.range2);
              Pulse_Syntax_Base.effect_tag =
                Pulse_Syntax_Base.default_effect_hint
            } in
          let body e2 =
            mk
              (Pulse_Syntax_Base.Tm_Bind
                 {
                   Pulse_Syntax_Base.binder = b_x;
                   Pulse_Syntax_Base.head1 = e2;
                   Pulse_Syntax_Base.body1 = e3
                 }) in
          match head.Pulse_Syntax_Base.term1 with
          | Pulse_Syntax_Base.Tm_TotBind
              { Pulse_Syntax_Base.binder1 = b_y;
                Pulse_Syntax_Base.head2 = e1; Pulse_Syntax_Base.body2 = e2;_}
              ->
              FStar_Pervasives_Native.Some
                (mk
                   (Pulse_Syntax_Base.Tm_TotBind
                      {
                        Pulse_Syntax_Base.binder1 = b_y;
                        Pulse_Syntax_Base.head2 = e1;
                        Pulse_Syntax_Base.body2 = (body e2)
                      }))
          | Pulse_Syntax_Base.Tm_Bind
              { Pulse_Syntax_Base.binder = b_y; Pulse_Syntax_Base.head1 = e1;
                Pulse_Syntax_Base.body1 = e2;_}
              ->
              FStar_Pervasives_Native.Some
                (mk
                   (Pulse_Syntax_Base.Tm_Bind
                      {
                        Pulse_Syntax_Base.binder = b_y;
                        Pulse_Syntax_Base.head1 = e1;
                        Pulse_Syntax_Base.body1 = (body e2)
                      }))
          | Pulse_Syntax_Base.Tm_WithLocal
              { Pulse_Syntax_Base.binder2 = b_y;
                Pulse_Syntax_Base.initializer1 = e1;
                Pulse_Syntax_Base.body4 = e2;_}
              ->
              FStar_Pervasives_Native.Some
                (mk
                   (Pulse_Syntax_Base.Tm_WithLocal
                      {
                        Pulse_Syntax_Base.binder2 = b_y;
                        Pulse_Syntax_Base.initializer1 = e1;
                        Pulse_Syntax_Base.body4 = (body e2)
                      }))
          | Pulse_Syntax_Base.Tm_WithLocalArray
              { Pulse_Syntax_Base.binder3 = b_y;
                Pulse_Syntax_Base.initializer2 = e1;
                Pulse_Syntax_Base.length = length;
                Pulse_Syntax_Base.body5 = e2;_}
              ->
              FStar_Pervasives_Native.Some
                (mk
                   (Pulse_Syntax_Base.Tm_WithLocalArray
                      {
                        Pulse_Syntax_Base.binder3 = b_y;
                        Pulse_Syntax_Base.initializer2 = e1;
                        Pulse_Syntax_Base.length = length;
                        Pulse_Syntax_Base.body5 = (body e2)
                      }))
          | uu___ -> FStar_Pervasives_Native.None
let rec (simplify_st_term :
  env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (353)) (Prims.of_int (16))
                 (Prims.of_int (353)) (Prims.of_int (31)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (353)) (Prims.of_int (36))
                 (Prims.of_int (415)) (Prims.of_int (27)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun t ->
                {
                  Pulse_Syntax_Base.term1 = t;
                  Pulse_Syntax_Base.range2 = (e.Pulse_Syntax_Base.range2);
                  Pulse_Syntax_Base.effect_tag =
                    (e.Pulse_Syntax_Base.effect_tag)
                }))
        (fun uu___ ->
           (fun ret ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (354)) (Prims.of_int (22))
                            (Prims.of_int (354)) (Prims.of_int (54)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (356)) (Prims.of_int (2))
                            (Prims.of_int (415)) (Prims.of_int (27)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         fun b -> fun e1 -> with_open g b e1 simplify_st_term))
                   (fun uu___ ->
                      (fun with_open1 ->
                         match e.Pulse_Syntax_Base.term1 with
                         | Pulse_Syntax_Base.Tm_Return uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_IntroPure uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_ElimExists uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_IntroExists uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_STApp uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_Rewrite uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_Admit uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_Abs
                             { Pulse_Syntax_Base.b = b;
                               Pulse_Syntax_Base.q = q;
                               Pulse_Syntax_Base.ascription = ascription;
                               Pulse_Syntax_Base.body = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (367))
                                              (Prims.of_int (8))
                                              (Prims.of_int (367))
                                              (Prims.of_int (62)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (367))
                                              (Prims.of_int (4))
                                              (Prims.of_int (367))
                                              (Prims.of_int (62)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (367))
                                                    (Prims.of_int (18))
                                                    (Prims.of_int (367))
                                                    (Prims.of_int (59)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (367))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (367))
                                                    (Prims.of_int (62)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (367))
                                                          (Prims.of_int (43))
                                                          (Prims.of_int (367))
                                                          (Prims.of_int (59)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (367))
                                                          (Prims.of_int (18))
                                                          (Prims.of_int (367))
                                                          (Prims.of_int (59)))))
                                                 (Obj.magic
                                                    (with_open1 b body))
                                                 (fun uu___ ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Syntax_Base.b
                                                             = b;
                                                           Pulse_Syntax_Base.q
                                                             = q;
                                                           Pulse_Syntax_Base.ascription
                                                             = ascription;
                                                           Pulse_Syntax_Base.body
                                                             = uu___
                                                         }))))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_Abs
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_Bind
                             { Pulse_Syntax_Base.binder = binder;
                               Pulse_Syntax_Base.head1 = head;
                               Pulse_Syntax_Base.body1 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (370))
                                              (Prims.of_int (29))
                                              (Prims.of_int (370))
                                              (Prims.of_int (54)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (371))
                                              (Prims.of_int (4))
                                              (Prims.of_int (387))
                                              (Prims.of_int (5)))))
                                     (Obj.magic (is_internal_binder binder))
                                     (fun uu___ ->
                                        (fun is_internal_binder1 ->
                                           if
                                             is_internal_binder1 &&
                                               (is_return_bv0 body)
                                           then
                                             Obj.magic
                                               (simplify_st_term g head)
                                           else
                                             if
                                               is_internal_binder1 &&
                                                 (FStar_Pervasives_Native.uu___is_Some
                                                    (is_return head))
                                             then
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (377))
                                                             (Prims.of_int (24))
                                                             (Prims.of_int (377))
                                                             (Prims.of_int (38)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (376))
                                                             (Prims.of_int (9))
                                                             (Prims.of_int (379))
                                                             (Prims.of_int (5)))))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          is_return head))
                                                    (fun uu___1 ->
                                                       (fun uu___1 ->
                                                          match uu___1 with
                                                          | FStar_Pervasives_Native.Some
                                                              head1 ->
                                                              Obj.magic
                                                                (simplify_st_term
                                                                   g
                                                                   (Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    head1)])))
                                                         uu___1))
                                             else
                                               (match simplify_nested_let e
                                                        binder head body
                                                with
                                                | FStar_Pervasives_Native.Some
                                                    e1 ->
                                                    Obj.magic
                                                      (simplify_st_term g e1)
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (384))
                                                                  (Prims.of_int (18))
                                                                  (Prims.of_int (384))
                                                                  (Prims.of_int (41)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (384))
                                                                  (Prims.of_int (44))
                                                                  (Prims.of_int (386))
                                                                  (Prims.of_int (43)))))
                                                         (Obj.magic
                                                            (simplify_st_term
                                                               g head))
                                                         (fun uu___2 ->
                                                            (fun head1 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (39)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (43)))))
                                                                    (
                                                                    Obj.magic
                                                                    (with_open1
                                                                    binder
                                                                    body))
                                                                    (
                                                                    fun body1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head1
                                                                    = head1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body1
                                                                    })))))
                                                              uu___2))))
                                          uu___)))
                         | Pulse_Syntax_Base.Tm_TotBind
                             { Pulse_Syntax_Base.binder1 = binder;
                               Pulse_Syntax_Base.head2 = head;
                               Pulse_Syntax_Base.body2 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (390))
                                              (Prims.of_int (8))
                                              (Prims.of_int (390))
                                              (Prims.of_int (67)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (390))
                                              (Prims.of_int (4))
                                              (Prims.of_int (390))
                                              (Prims.of_int (67)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (390))
                                                    (Prims.of_int (22))
                                                    (Prims.of_int (390))
                                                    (Prims.of_int (64)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (390))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (390))
                                                    (Prims.of_int (67)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (390))
                                                          (Prims.of_int (43))
                                                          (Prims.of_int (390))
                                                          (Prims.of_int (64)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (390))
                                                          (Prims.of_int (22))
                                                          (Prims.of_int (390))
                                                          (Prims.of_int (64)))))
                                                 (Obj.magic
                                                    (with_open1 binder body))
                                                 (fun uu___ ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Syntax_Base.binder1
                                                             = binder;
                                                           Pulse_Syntax_Base.head2
                                                             = head;
                                                           Pulse_Syntax_Base.body2
                                                             = uu___
                                                         }))))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_TotBind
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_If
                             { Pulse_Syntax_Base.b1 = b;
                               Pulse_Syntax_Base.then_ = then_;
                               Pulse_Syntax_Base.else_ = else_;
                               Pulse_Syntax_Base.post1 = post;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (393))
                                              (Prims.of_int (8))
                                              (Prims.of_int (393))
                                              (Prims.of_int (95)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (393))
                                              (Prims.of_int (4))
                                              (Prims.of_int (393))
                                              (Prims.of_int (95)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (393))
                                                    (Prims.of_int (17))
                                                    (Prims.of_int (393))
                                                    (Prims.of_int (92)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (393))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (393))
                                                    (Prims.of_int (95)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (393))
                                                          (Prims.of_int (28))
                                                          (Prims.of_int (393))
                                                          (Prims.of_int (52)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (393))
                                                          (Prims.of_int (17))
                                                          (Prims.of_int (393))
                                                          (Prims.of_int (92)))))
                                                 (Obj.magic
                                                    (simplify_st_term g then_))
                                                 (fun uu___ ->
                                                    (fun uu___ ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (86)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (92)))))
                                                            (Obj.magic
                                                               (simplify_st_term
                                                                  g else_))
                                                            (fun uu___1 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___2
                                                                    ->
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b;
                                                                    Pulse_Syntax_Base.then_
                                                                    = uu___;
                                                                    Pulse_Syntax_Base.else_
                                                                    = uu___1;
                                                                    Pulse_Syntax_Base.post1
                                                                    = post
                                                                    }))))
                                                      uu___)))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_If
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_Match
                             { Pulse_Syntax_Base.sc = sc;
                               Pulse_Syntax_Base.returns_ = returns_;
                               Pulse_Syntax_Base.brs = brs;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (396))
                                              (Prims.of_int (8))
                                              (Prims.of_int (396))
                                              (Prims.of_int (72)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (396))
                                              (Prims.of_int (4))
                                              (Prims.of_int (396))
                                              (Prims.of_int (72)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (396))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (396))
                                                    (Prims.of_int (69)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (396))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (396))
                                                    (Prims.of_int (72)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (396))
                                                          (Prims.of_int (40))
                                                          (Prims.of_int (396))
                                                          (Prims.of_int (69)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (396))
                                                          (Prims.of_int (20))
                                                          (Prims.of_int (396))
                                                          (Prims.of_int (69)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Util.map
                                                       (simplify_branch g)
                                                       brs))
                                                 (fun uu___ ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Syntax_Base.sc
                                                             = sc;
                                                           Pulse_Syntax_Base.returns_
                                                             = returns_;
                                                           Pulse_Syntax_Base.brs
                                                             = uu___
                                                         }))))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_Match
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_While
                             { Pulse_Syntax_Base.invariant = invariant;
                               Pulse_Syntax_Base.condition = condition;
                               Pulse_Syntax_Base.condition_var =
                                 condition_var;
                               Pulse_Syntax_Base.body3 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (399))
                                              (Prims.of_int (20))
                                              (Prims.of_int (399))
                                              (Prims.of_int (48)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (399))
                                              (Prims.of_int (51))
                                              (Prims.of_int (401))
                                              (Prims.of_int (76)))))
                                     (Obj.magic
                                        (simplify_st_term g condition))
                                     (fun uu___ ->
                                        (fun condition1 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (400))
                                                         (Prims.of_int (15))
                                                         (Prims.of_int (400))
                                                         (Prims.of_int (38)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (401))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (401))
                                                         (Prims.of_int (74)))))
                                                (Obj.magic
                                                   (simplify_st_term g body))
                                                (fun body1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___ ->
                                                        {
                                                          Pulse_Syntax_Base.term1
                                                            =
                                                            (Pulse_Syntax_Base.Tm_While
                                                               {
                                                                 Pulse_Syntax_Base.invariant
                                                                   =
                                                                   invariant;
                                                                 Pulse_Syntax_Base.condition
                                                                   =
                                                                   condition1;
                                                                 Pulse_Syntax_Base.condition_var
                                                                   =
                                                                   condition_var;
                                                                 Pulse_Syntax_Base.body3
                                                                   = body1
                                                               });
                                                          Pulse_Syntax_Base.range2
                                                            =
                                                            (e.Pulse_Syntax_Base.range2);
                                                          Pulse_Syntax_Base.effect_tag
                                                            =
                                                            (e.Pulse_Syntax_Base.effect_tag)
                                                        })))) uu___)))
                         | Pulse_Syntax_Base.Tm_Par
                             { Pulse_Syntax_Base.pre1 = pre1;
                               Pulse_Syntax_Base.body11 = body1;
                               Pulse_Syntax_Base.post11 = post1;
                               Pulse_Syntax_Base.pre2 = pre2;
                               Pulse_Syntax_Base.body21 = body2;
                               Pulse_Syntax_Base.post2 = post2;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (404))
                                              (Prims.of_int (16))
                                              (Prims.of_int (404))
                                              (Prims.of_int (40)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (404))
                                              (Prims.of_int (43))
                                              (Prims.of_int (406))
                                              (Prims.of_int (71)))))
                                     (Obj.magic (simplify_st_term g body1))
                                     (fun uu___ ->
                                        (fun body11 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (405))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (405))
                                                         (Prims.of_int (40)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (406))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (406))
                                                         (Prims.of_int (69)))))
                                                (Obj.magic
                                                   (simplify_st_term g body2))
                                                (fun body21 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___ ->
                                                        {
                                                          Pulse_Syntax_Base.term1
                                                            =
                                                            (Pulse_Syntax_Base.Tm_Par
                                                               {
                                                                 Pulse_Syntax_Base.pre1
                                                                   = pre1;
                                                                 Pulse_Syntax_Base.body11
                                                                   = body11;
                                                                 Pulse_Syntax_Base.post11
                                                                   = post1;
                                                                 Pulse_Syntax_Base.pre2
                                                                   = pre2;
                                                                 Pulse_Syntax_Base.body21
                                                                   = body21;
                                                                 Pulse_Syntax_Base.post2
                                                                   = post2
                                                               });
                                                          Pulse_Syntax_Base.range2
                                                            =
                                                            (e.Pulse_Syntax_Base.range2);
                                                          Pulse_Syntax_Base.effect_tag
                                                            =
                                                            (e.Pulse_Syntax_Base.effect_tag)
                                                        })))) uu___)))
                         | Pulse_Syntax_Base.Tm_WithLocal
                             { Pulse_Syntax_Base.binder2 = binder;
                               Pulse_Syntax_Base.initializer1 = initializer1;
                               Pulse_Syntax_Base.body4 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (409))
                                              (Prims.of_int (8))
                                              (Prims.of_int (409))
                                              (Prims.of_int (76)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (409))
                                              (Prims.of_int (4))
                                              (Prims.of_int (409))
                                              (Prims.of_int (76)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (409))
                                                    (Prims.of_int (24))
                                                    (Prims.of_int (409))
                                                    (Prims.of_int (73)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (409))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (409))
                                                    (Prims.of_int (76)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (409))
                                                          (Prims.of_int (52))
                                                          (Prims.of_int (409))
                                                          (Prims.of_int (73)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (409))
                                                          (Prims.of_int (24))
                                                          (Prims.of_int (409))
                                                          (Prims.of_int (73)))))
                                                 (Obj.magic
                                                    (with_open1 binder body))
                                                 (fun uu___ ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Syntax_Base.binder2
                                                             = binder;
                                                           Pulse_Syntax_Base.initializer1
                                                             = initializer1;
                                                           Pulse_Syntax_Base.body4
                                                             = uu___
                                                         }))))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_WithLocal
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_WithLocalArray
                             { Pulse_Syntax_Base.binder3 = binder;
                               Pulse_Syntax_Base.initializer2 = initializer1;
                               Pulse_Syntax_Base.length = length;
                               Pulse_Syntax_Base.body5 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (412))
                                              (Prims.of_int (8))
                                              (Prims.of_int (412))
                                              (Prims.of_int (89)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (412))
                                              (Prims.of_int (4))
                                              (Prims.of_int (412))
                                              (Prims.of_int (89)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (412))
                                                    (Prims.of_int (29))
                                                    (Prims.of_int (412))
                                                    (Prims.of_int (86)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (412))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (412))
                                                    (Prims.of_int (89)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (412))
                                                          (Prims.of_int (65))
                                                          (Prims.of_int (412))
                                                          (Prims.of_int (86)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (412))
                                                          (Prims.of_int (29))
                                                          (Prims.of_int (412))
                                                          (Prims.of_int (86)))))
                                                 (Obj.magic
                                                    (with_open1 binder body))
                                                 (fun uu___ ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Syntax_Base.binder3
                                                             = binder;
                                                           Pulse_Syntax_Base.initializer2
                                                             = initializer1;
                                                           Pulse_Syntax_Base.length
                                                             = length;
                                                           Pulse_Syntax_Base.body5
                                                             = uu___
                                                         }))))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_WithLocalArray
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_WithInv
                             { Pulse_Syntax_Base.name1 = uu___;
                               Pulse_Syntax_Base.body6 = body;
                               Pulse_Syntax_Base.returns_inv = uu___1;_}
                             ->
                             Obj.magic (Obj.repr (simplify_st_term g body)))
                        uu___))) uu___)
and (simplify_branch :
  env ->
    Pulse_Syntax_Base.branch ->
      (Pulse_Syntax_Base.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (418)) (Prims.of_int (18))
                 (Prims.of_int (418)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (417)) (Prims.of_int (55))
                 (Prims.of_int (422)) (Prims.of_int (62)))))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> b))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (pat, body) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (419)) (Prims.of_int (17))
                                (Prims.of_int (419)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (418)) (Prims.of_int (22))
                                (Prims.of_int (422)) (Prims.of_int (62)))))
                       (Obj.magic (extend_env_pat g pat))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | (g1, uu___2, bs) ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (420))
                                               (Prims.of_int (13))
                                               (Prims.of_int (420))
                                               (Prims.of_int (56)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (420))
                                               (Prims.of_int (59))
                                               (Prims.of_int (422))
                                               (Prims.of_int (62)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            Pulse_Checker_Match.open_st_term_bs
                                              body bs))
                                      (fun uu___3 ->
                                         (fun body1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (421))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (421))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (422))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (422))
                                                          (Prims.of_int (62)))))
                                                 (Obj.magic
                                                    (simplify_st_term g1
                                                       body1))
                                                 (fun body2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         (pat,
                                                           (Pulse_Syntax_Naming.close_st_term_n
                                                              body2
                                                              (FStar_List_Tot_Base.map
                                                                 FStar_Pervasives_Native.fst
                                                                 bs)))))))
                                           uu___3))) uu___1))) uu___)
let (erase_type_for_extraction :
  env ->
    Pulse_Syntax_Base.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   match t.Pulse_Syntax_Base.t with
                   | Pulse_Syntax_Base.Tm_FStar t1 ->
                       Pulse_RuntimeUtils.must_erase_for_extraction
                         (tcenv_of_env g) t1
                   | uu___1 -> false))) uu___1 uu___
let rec (erase_ghost_subterms :
  env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (432)) (Prims.of_int (22))
                 (Prims.of_int (432)) (Prims.of_int (50)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (432)) (Prims.of_int (53))
                 (Prims.of_int (508)) (Prims.of_int (5)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> fun g1 -> Pulse_Typing_Env.fresh g1.coreenv))
        (fun uu___ ->
           (fun fresh1 ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (434)) (Prims.of_int (6))
                            (Prims.of_int (434)) (Prims.of_int (77)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (434)) (Prims.of_int (82))
                            (Prims.of_int (508)) (Prims.of_int (5)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         fun g1 ->
                           fun x ->
                             fun b ->
                               {
                                 uenv_inner = (g1.uenv_inner);
                                 coreenv =
                                   (Pulse_Typing_Env.push_binding g1.coreenv
                                      x b.Pulse_Syntax_Base.binder_ppname
                                      b.Pulse_Syntax_Base.binder_ty)
                               }))
                   (fun uu___ ->
                      (fun push_binding1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (436))
                                       (Prims.of_int (71))
                                       (Prims.of_int (440))
                                       (Prims.of_int (24)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (440))
                                       (Prims.of_int (27))
                                       (Prims.of_int (508))
                                       (Prims.of_int (5)))))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ ->
                                    fun g1 ->
                                      fun b ->
                                        fun e ->
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (437))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (437))
                                                     (Prims.of_int (19)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (437))
                                                     (Prims.of_int (22))
                                                     (Prims.of_int (440))
                                                     (Prims.of_int (24)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 -> fresh1 g1))
                                            (fun uu___1 ->
                                               (fun x ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (438))
                                                                (Prims.of_int (12))
                                                                (Prims.of_int (438))
                                                                (Prims.of_int (84)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (438))
                                                                (Prims.of_int (87))
                                                                (Prims.of_int (440))
                                                                (Prims.of_int (24)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___1 ->
                                                             Pulse_Syntax_Naming.open_st_term'
                                                               e
                                                               (Pulse_Syntax_Pure.tm_var
                                                                  {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    =
                                                                    (b.Pulse_Syntax_Base.binder_ppname)
                                                                  })
                                                               Prims.int_zero))
                                                       (fun uu___1 ->
                                                          (fun e1 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (55)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (24)))))
                                                                  (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    (push_binding1
                                                                    g1 x b)
                                                                    e1))
                                                                  (fun e2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Naming.close_st_term'
                                                                    e2 x
                                                                    Prims.int_zero))))
                                                            uu___1))) uu___1)))
                              (fun uu___ ->
                                 (fun open_erase_close ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (443))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (443))
                                                  (Prims.of_int (80)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (444))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (508))
                                                  (Prims.of_int (5)))))
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___ ->
                                               {
                                                 Pulse_Syntax_Base.term1 =
                                                   (Pulse_Syntax_Base.Tm_Return
                                                      {
                                                        Pulse_Syntax_Base.ctag
                                                          =
                                                          Pulse_Syntax_Base.STT;
                                                        Pulse_Syntax_Base.insert_eq
                                                          = false;
                                                        Pulse_Syntax_Base.term
                                                          = unit_val
                                                      });
                                                 Pulse_Syntax_Base.range2 =
                                                   (p.Pulse_Syntax_Base.range2);
                                                 Pulse_Syntax_Base.effect_tag
                                                   =
                                                   (p.Pulse_Syntax_Base.effect_tag)
                                               }))
                                         (fun uu___ ->
                                            (fun unit_tm ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (445))
                                                             (Prims.of_int (27))
                                                             (Prims.of_int (445))
                                                             (Prims.of_int (42)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (446))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (508))
                                                             (Prims.of_int (5)))))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___ ->
                                                          fun t ->
                                                            {
                                                              Pulse_Syntax_Base.term1
                                                                = t;
                                                              Pulse_Syntax_Base.range2
                                                                =
                                                                (p.Pulse_Syntax_Base.range2);
                                                              Pulse_Syntax_Base.effect_tag
                                                                =
                                                                (p.Pulse_Syntax_Base.effect_tag)
                                                            }))
                                                    (fun uu___ ->
                                                       (fun ret ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (18)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (508))
                                                                    (Prims.of_int (5)))))
                                                               (Obj.magic
                                                                  (is_erasable
                                                                    p))
                                                               (fun uu___ ->
                                                                  (fun uu___
                                                                    ->
                                                                    if uu___
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    unit_tm)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    p.Pulse_Syntax_Base.term1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_IntroPure
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    unit_tm))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_ElimExists
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    unit_tm))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_IntroExists
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    unit_tm))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Rewrite
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    unit_tm))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Admit
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    p))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (458))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (458))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (open_erase_close
                                                                    g b body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    = body1
                                                                    }))))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Return
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    p))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_STApp
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    p))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head1
                                                                    = head;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (is_erasable
                                                                    head))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    if uu___2
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    unit_val)]))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body1))
                                                                    uu___3))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g head))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    head1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (470))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (470))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (open_erase_close
                                                                    g binder
                                                                    body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head1
                                                                    = head1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body1
                                                                    })))))
                                                                    uu___4)))
                                                                    uu___2))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_TotBind
                                                                    {
                                                                    Pulse_Syntax_Base.binder1
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head2
                                                                    = head;
                                                                    Pulse_Syntax_Base.body2
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (erase_type_for_extraction
                                                                    g
                                                                    binder.Pulse_Syntax_Base.binder_ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    if uu___2
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    unit_val)]))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body1))
                                                                    uu___3))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (open_erase_close
                                                                    g binder
                                                                    body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_TotBind
                                                                    {
                                                                    Pulse_Syntax_Base.binder1
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head2
                                                                    = head;
                                                                    Pulse_Syntax_Base.body2
                                                                    = body1
                                                                    })))))
                                                                    uu___2))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_If
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b;
                                                                    Pulse_Syntax_Base.then_
                                                                    = then_;
                                                                    Pulse_Syntax_Base.else_
                                                                    = else_;
                                                                    Pulse_Syntax_Base.post1
                                                                    = post;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g then_))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    then_1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g else_))
                                                                    (fun
                                                                    else_1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_If
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b;
                                                                    Pulse_Syntax_Base.then_
                                                                    = then_1;
                                                                    Pulse_Syntax_Base.else_
                                                                    = else_1;
                                                                    Pulse_Syntax_Base.post1
                                                                    = post
                                                                    })))))
                                                                    uu___2))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Match
                                                                    {
                                                                    Pulse_Syntax_Base.sc
                                                                    = sc;
                                                                    Pulse_Syntax_Base.returns_
                                                                    =
                                                                    returns_;
                                                                    Pulse_Syntax_Base.brs
                                                                    = brs;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (erase_ghost_subterms_branch
                                                                    g) brs))
                                                                    (fun brs1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_Match
                                                                    {
                                                                    Pulse_Syntax_Base.sc
                                                                    = sc;
                                                                    Pulse_Syntax_Base.returns_
                                                                    =
                                                                    returns_;
                                                                    Pulse_Syntax_Base.brs
                                                                    = brs1
                                                                    }))))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_While
                                                                    {
                                                                    Pulse_Syntax_Base.invariant
                                                                    =
                                                                    invariant;
                                                                    Pulse_Syntax_Base.condition
                                                                    =
                                                                    condition;
                                                                    Pulse_Syntax_Base.condition_var
                                                                    =
                                                                    condition_var;
                                                                    Pulse_Syntax_Base.body3
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g
                                                                    condition))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    condition1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_While
                                                                    {
                                                                    Pulse_Syntax_Base.invariant
                                                                    =
                                                                    invariant;
                                                                    Pulse_Syntax_Base.condition
                                                                    =
                                                                    condition1;
                                                                    Pulse_Syntax_Base.condition_var
                                                                    =
                                                                    condition_var;
                                                                    Pulse_Syntax_Base.body3
                                                                    = body1
                                                                    })))))
                                                                    uu___2))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre1
                                                                    = pre1;
                                                                    Pulse_Syntax_Base.body11
                                                                    = body1;
                                                                    Pulse_Syntax_Base.post11
                                                                    = post1;
                                                                    Pulse_Syntax_Base.pre2
                                                                    = pre2;
                                                                    Pulse_Syntax_Base.body21
                                                                    = body2;
                                                                    Pulse_Syntax_Base.post2
                                                                    = post2;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    body11 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body2))
                                                                    (fun
                                                                    body21 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre1
                                                                    = pre1;
                                                                    Pulse_Syntax_Base.body11
                                                                    = body11;
                                                                    Pulse_Syntax_Base.post11
                                                                    = post1;
                                                                    Pulse_Syntax_Base.pre2
                                                                    = pre2;
                                                                    Pulse_Syntax_Base.body21
                                                                    = body21;
                                                                    Pulse_Syntax_Base.post2
                                                                    = post2
                                                                    })))))
                                                                    uu___2))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_WithLocal
                                                                    {
                                                                    Pulse_Syntax_Base.binder2
                                                                    = binder;
                                                                    Pulse_Syntax_Base.initializer1
                                                                    =
                                                                    initializer1;
                                                                    Pulse_Syntax_Base.body4
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (open_erase_close
                                                                    g binder
                                                                    body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_WithLocal
                                                                    {
                                                                    Pulse_Syntax_Base.binder2
                                                                    = binder;
                                                                    Pulse_Syntax_Base.initializer1
                                                                    =
                                                                    initializer1;
                                                                    Pulse_Syntax_Base.body4
                                                                    = body1
                                                                    }))))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_WithLocalArray
                                                                    {
                                                                    Pulse_Syntax_Base.binder3
                                                                    = binder;
                                                                    Pulse_Syntax_Base.initializer2
                                                                    =
                                                                    initializer1;
                                                                    Pulse_Syntax_Base.length
                                                                    = length;
                                                                    Pulse_Syntax_Base.body5
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (open_erase_close
                                                                    g binder
                                                                    body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_WithLocalArray
                                                                    {
                                                                    Pulse_Syntax_Base.binder3
                                                                    = binder;
                                                                    Pulse_Syntax_Base.initializer2
                                                                    =
                                                                    initializer1;
                                                                    Pulse_Syntax_Base.length
                                                                    = length;
                                                                    Pulse_Syntax_Base.body5
                                                                    = body1
                                                                    }))))
                                                                    | 
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Unexpected st term when erasing ghost subterms"))))
                                                                    uu___)))
                                                         uu___))) uu___)))
                                   uu___))) uu___))) uu___)
and (erase_ghost_subterms_branch :
  env ->
    Pulse_Syntax_Base.branch ->
      (Pulse_Syntax_Base.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (511)) (Prims.of_int (18))
                 (Prims.of_int (511)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (510)) (Prims.of_int (67))
                 (Prims.of_int (515)) (Prims.of_int (62)))))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> b))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (pat, body) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (512)) (Prims.of_int (17))
                                (Prims.of_int (512)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (511)) (Prims.of_int (22))
                                (Prims.of_int (515)) (Prims.of_int (62)))))
                       (Obj.magic (extend_env_pat g pat))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | (g1, uu___2, bs) ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (513))
                                               (Prims.of_int (13))
                                               (Prims.of_int (513))
                                               (Prims.of_int (56)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (513))
                                               (Prims.of_int (59))
                                               (Prims.of_int (515))
                                               (Prims.of_int (62)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            Pulse_Checker_Match.open_st_term_bs
                                              body bs))
                                      (fun uu___3 ->
                                         (fun body1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (514))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (514))
                                                          (Prims.of_int (40)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (515))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (515))
                                                          (Prims.of_int (62)))))
                                                 (Obj.magic
                                                    (erase_ghost_subterms g1
                                                       body1))
                                                 (fun body2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         (pat,
                                                           (Pulse_Syntax_Naming.close_st_term_n
                                                              body2
                                                              (FStar_List_Tot_Base.map
                                                                 FStar_Pervasives_Native.fst
                                                                 bs)))))))
                                           uu___3))) uu___1))) uu___)
let rec (extract :
  env ->
    Pulse_Syntax_Base.st_term ->
      ((Pulse_Extract_CompilerLib.mlexpr * Pulse_Extract_CompilerLib.e_tag),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (519)) (Prims.of_int (24))
                 (Prims.of_int (519)) (Prims.of_int (48)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (520)) (Prims.of_int (4)) (Prims.of_int (655))
                 (Prims.of_int (7)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              (Pulse_Extract_CompilerLib.mle_unit,
                Pulse_Extract_CompilerLib.e_tag_erasable)))
        (fun uu___ ->
           (fun erased_result ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (520)) (Prims.of_int (4))
                            (Prims.of_int (522)) (Prims.of_int (36)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (523)) (Prims.of_int (4))
                            (Prims.of_int (655)) (Prims.of_int (7)))))
                   (Obj.magic
                      (debug g
                         (fun uu___ ->
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (522))
                                       (Prims.of_int (14))
                                       (Prims.of_int (522))
                                       (Prims.of_int (35)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (520))
                                       (Prims.of_int (22))
                                       (Prims.of_int (522))
                                       (Prims.of_int (35)))))
                              (Obj.magic
                                 (Pulse_Syntax_Printer.st_term_to_string p))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (520))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (522))
                                                  (Prims.of_int (35)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (520))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (522))
                                                  (Prims.of_int (35)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Extract.Main.fst"
                                                        (Prims.of_int (521))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (521))
                                                        (Prims.of_int (41)))))
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
                                                     p.Pulse_Syntax_Base.range2))
                                               (fun uu___2 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___3 ->
                                                       fun x ->
                                                         Prims.strcat
                                                           (Prims.strcat
                                                              "Extracting term@"
                                                              (Prims.strcat
                                                                 uu___2 ":\n"))
                                                           (Prims.strcat x
                                                              "\n")))))
                                         (fun uu___2 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 -> uu___2 uu___1))))
                                   uu___1))))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (523))
                                       (Prims.of_int (7))
                                       (Prims.of_int (523))
                                       (Prims.of_int (20)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (523))
                                       (Prims.of_int (4))
                                       (Prims.of_int (655))
                                       (Prims.of_int (7)))))
                              (Obj.magic (is_erasable p))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    if uu___1
                                    then
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 -> erased_result)))
                                    else
                                      Obj.magic
                                        (Obj.repr
                                           (match p.Pulse_Syntax_Base.term1
                                            with
                                            | Pulse_Syntax_Base.Tm_IntroPure
                                                uu___3 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_ElimExists
                                                uu___3 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_IntroExists
                                                uu___3 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_Rewrite
                                                uu___3 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_Abs
                                                { Pulse_Syntax_Base.b = b;
                                                  Pulse_Syntax_Base.q = q;
                                                  Pulse_Syntax_Base.ascription
                                                    = uu___3;
                                                  Pulse_Syntax_Base.body =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (534))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (534))
                                                              (Prims.of_int (51)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (533))
                                                              (Prims.of_int (32))
                                                              (Prims.of_int (538))
                                                              (Prims.of_int (23)))))
                                                     (Obj.magic
                                                        (extend_env g b))
                                                     (fun uu___4 ->
                                                        (fun uu___4 ->
                                                           match uu___4 with
                                                           | (g1, mlident,
                                                              mlty, name1) ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (47)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (23)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___7)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    (mlident,
                                                                    mlty)]
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_pure)))))
                                                                    uu___5)))
                                                          uu___4))
                                            | Pulse_Syntax_Base.Tm_Return
                                                {
                                                  Pulse_Syntax_Base.ctag =
                                                    uu___3;
                                                  Pulse_Syntax_Base.insert_eq
                                                    = uu___4;
                                                  Pulse_Syntax_Base.term =
                                                    term;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (541))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (541))
                                                              (Prims.of_int (29)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (541))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (542))
                                                              (Prims.of_int (18)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g
                                                           term))
                                                     (fun uu___5 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___6 ->
                                                             (uu___5,
                                                               Pulse_Extract_CompilerLib.e_tag_pure))))
                                            | Pulse_Syntax_Base.Tm_STApp
                                                {
                                                  Pulse_Syntax_Base.head =
                                                    head;
                                                  Pulse_Syntax_Base.arg_qual
                                                    = uu___3;
                                                  Pulse_Syntax_Base.arg = arg;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (545))
                                                              (Prims.of_int (14))
                                                              (Prims.of_int (545))
                                                              (Prims.of_int (37)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (544))
                                                              (Prims.of_int (34))
                                                              (Prims.of_int (553))
                                                              (Prims.of_int (7)))))
                                                     (Obj.magic
                                                        (maybe_inline g head
                                                           arg))
                                                     (fun uu___4 ->
                                                        (fun uu___4 ->
                                                           match uu___4 with
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (42)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (42)))))
                                                                    (
                                                                    Obj.magic
                                                                    (term_as_mlexpr
                                                                    g head))
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    head1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (548))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (548))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (term_as_mlexpr
                                                                    g arg))
                                                                    (fun arg1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ((Pulse_Extract_CompilerLib.mle_app
                                                                    head1
                                                                    [arg1]),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___5))
                                                           | FStar_Pervasives_Native.Some
                                                               t ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (84)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (552))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (552))
                                                                    (Prims.of_int (21)))))
                                                                    (
                                                                    Obj.magic
                                                                    (debug g
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    t))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "Inlined to: "
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    "\n"))))))
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (extract
                                                                    g t))
                                                                    uu___5)))
                                                          uu___4))
                                            | Pulse_Syntax_Base.Tm_Bind
                                                {
                                                  Pulse_Syntax_Base.binder =
                                                    binder;
                                                  Pulse_Syntax_Base.head1 =
                                                    head;
                                                  Pulse_Syntax_Base.body1 =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (556))
                                                              (Prims.of_int (11))
                                                              (Prims.of_int (556))
                                                              (Prims.of_int (27)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (556))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (572))
                                                              (Prims.of_int (9)))))
                                                     (Obj.magic
                                                        (is_erasable head))
                                                     (fun uu___3 ->
                                                        (fun uu___3 ->
                                                           if uu___3
                                                           then
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (558))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (558))
                                                                    (Prims.of_int (61)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (24)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    unit_val)]))
                                                                  (fun uu___4
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    (debug g
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    body1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    head))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Erasing head of bind "
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    "\nopened body to "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6
                                                                    uu___5))))
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (extract
                                                                    g body1))
                                                                    uu___4)))
                                                                    uu___4))
                                                           else
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (565))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (565))
                                                                    (Prims.of_int (38)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (564))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (9)))))
                                                                  (Obj.magic
                                                                    (extract
                                                                    g head))
                                                                  (fun uu___5
                                                                    ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (head1,
                                                                    uu___6)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (566))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (566))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (565))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (extend_env
                                                                    g binder))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    mlident,
                                                                    mlty,
                                                                    name1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (567))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (567))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (567))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (568))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (568))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (567))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___10)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_let
                                                                    (Pulse_Extract_CompilerLib.mk_mlletbinding
                                                                    false
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mllb
                                                                    mlident
                                                                    ([],
                                                                    mlty)
                                                                    head1])
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___5)))
                                                          uu___3))
                                            | Pulse_Syntax_Base.Tm_TotBind
                                                {
                                                  Pulse_Syntax_Base.binder1 =
                                                    binder;
                                                  Pulse_Syntax_Base.head2 =
                                                    head;
                                                  Pulse_Syntax_Base.body2 =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (576))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (576))
                                                              (Prims.of_int (40)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (576))
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (582))
                                                              (Prims.of_int (47)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g
                                                           head))
                                                     (fun uu___3 ->
                                                        (fun head1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (577))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (577))
                                                                    (Prims.of_int (56)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (47)))))
                                                                (Obj.magic
                                                                   (extend_env
                                                                    g binder))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    mlident,
                                                                    mlty,
                                                                    name1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___6)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_let
                                                                    (Pulse_Extract_CompilerLib.mk_mlletbinding
                                                                    false
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mllb
                                                                    mlident
                                                                    ([],
                                                                    mlty)
                                                                    head1])
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___4)))
                                                                    uu___3)))
                                                          uu___3))
                                            | Pulse_Syntax_Base.Tm_If
                                                { Pulse_Syntax_Base.b1 = b;
                                                  Pulse_Syntax_Base.then_ =
                                                    then_;
                                                  Pulse_Syntax_Base.else_ =
                                                    else_;
                                                  Pulse_Syntax_Base.post1 =
                                                    uu___3;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (585))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (585))
                                                              (Prims.of_int (34)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (585))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (588))
                                                              (Prims.of_int (49)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g b))
                                                     (fun uu___4 ->
                                                        (fun b1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (586))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (586))
                                                                    (Prims.of_int (38)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (49)))))
                                                                (Obj.magic
                                                                   (extract g
                                                                    then_))
                                                                (fun uu___4
                                                                   ->
                                                                   (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (then_1,
                                                                    uu___5)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (587))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (587))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (586))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g else_))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (else_1,
                                                                    uu___8)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_if
                                                                    b1 then_1
                                                                    (FStar_Pervasives_Native.Some
                                                                    else_1)),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___4)))
                                                          uu___4))
                                            | Pulse_Syntax_Base.Tm_Match
                                                { Pulse_Syntax_Base.sc = sc;
                                                  Pulse_Syntax_Base.returns_
                                                    = uu___3;
                                                  Pulse_Syntax_Base.brs = brs;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (591))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (591))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (591))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (603))
                                                              (Prims.of_int (38)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g sc))
                                                     (fun uu___4 ->
                                                        (fun sc1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (592))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (19)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (38)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___4 ->
                                                                    fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (pat0,
                                                                    body) ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (592))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (extend_env_pat
                                                                    g pat0))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (g1, pat,
                                                                    bs) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (debug g1
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (596))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (596))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.pattern_to_string
                                                                    pat0))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Extracting branch with pattern "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Checker_Match.open_st_term_bs
                                                                    body bs))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___10)
                                                                    ->
                                                                    (pat,
                                                                    body2)))))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                (fun uu___4
                                                                   ->
                                                                   (fun
                                                                    extract_branch
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    extract_branch
                                                                    brs))
                                                                    (fun brs1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ((Pulse_Extract_CompilerLib.mle_match
                                                                    sc1 brs1),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___4)))
                                                          uu___4))
                                            | Pulse_Syntax_Base.Tm_While
                                                {
                                                  Pulse_Syntax_Base.invariant
                                                    = uu___3;
                                                  Pulse_Syntax_Base.condition
                                                    = condition;
                                                  Pulse_Syntax_Base.condition_var
                                                    = uu___4;
                                                  Pulse_Syntax_Base.body3 =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (607))
                                                              (Prims.of_int (27))
                                                              (Prims.of_int (607))
                                                              (Prims.of_int (46)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (612))
                                                              (Prims.of_int (23)))))
                                                     (Obj.magic
                                                        (extract g condition))
                                                     (fun uu___5 ->
                                                        (fun uu___5 ->
                                                           match uu___5 with
                                                           | (condition1,
                                                              uu___6) ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (36)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (612))
                                                                    (Prims.of_int (23)))))
                                                                    (
                                                                    Obj.magic
                                                                    (extract
                                                                    g body))
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (body1,
                                                                    uu___9)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_app
                                                                    (Pulse_Extract_CompilerLib.mle_name
                                                                    (["Pulse";
                                                                    "Lib";
                                                                    "Core"],
                                                                    "while_"))
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    ("_",
                                                                    Pulse_Extract_CompilerLib.mlty_unit)]
                                                                    condition1;
                                                                    Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    ("_",
                                                                    Pulse_Extract_CompilerLib.mlty_unit)]
                                                                    body1]),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                          uu___5))
                                            | Pulse_Syntax_Base.Tm_Par
                                                {
                                                  Pulse_Syntax_Base.pre1 =
                                                    uu___3;
                                                  Pulse_Syntax_Base.body11 =
                                                    body1;
                                                  Pulse_Syntax_Base.post11 =
                                                    uu___4;
                                                  Pulse_Syntax_Base.pre2 =
                                                    uu___5;
                                                  Pulse_Syntax_Base.body21 =
                                                    body2;
                                                  Pulse_Syntax_Base.post2 =
                                                    uu___6;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (615))
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (615))
                                                              (Prims.of_int (38)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (614))
                                                              (Prims.of_int (34))
                                                              (Prims.of_int (620))
                                                              (Prims.of_int (23)))))
                                                     (Obj.magic
                                                        (extract g body1))
                                                     (fun uu___7 ->
                                                        (fun uu___7 ->
                                                           match uu___7 with
                                                           | (body11, uu___8)
                                                               ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (38)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (23)))))
                                                                    (
                                                                    Obj.magic
                                                                    (extract
                                                                    g body2))
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (body21,
                                                                    uu___11)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_app
                                                                    (Pulse_Extract_CompilerLib.mle_name
                                                                    (["Pulse";
                                                                    "Lib";
                                                                    "Core"],
                                                                    "par"))
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    ("_",
                                                                    Pulse_Extract_CompilerLib.mlty_unit)]
                                                                    body11;
                                                                    Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    ("_",
                                                                    Pulse_Extract_CompilerLib.mlty_unit)]
                                                                    body21]),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                          uu___7))
                                            | Pulse_Syntax_Base.Tm_WithLocal
                                                {
                                                  Pulse_Syntax_Base.binder2 =
                                                    binder;
                                                  Pulse_Syntax_Base.initializer1
                                                    = initializer1;
                                                  Pulse_Syntax_Base.body4 =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (623))
                                                              (Prims.of_int (26))
                                                              (Prims.of_int (623))
                                                              (Prims.of_int (54)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (623))
                                                              (Prims.of_int (57))
                                                              (Prims.of_int (630))
                                                              (Prims.of_int (47)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g
                                                           initializer1))
                                                     (fun uu___3 ->
                                                        (fun initializer2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (94)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (47)))))
                                                                (Obj.magic
                                                                   (extend_env
                                                                    g
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_ty);
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_ppname)
                                                                    }))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    mlident,
                                                                    mlty,
                                                                    name1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___6)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_let
                                                                    (Pulse_Extract_CompilerLib.mk_mlletbinding
                                                                    false
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mut_mllb
                                                                    mlident
                                                                    ([],
                                                                    mlty)
                                                                    (Pulse_Extract_CompilerLib.mle_app
                                                                    (Pulse_Extract_CompilerLib.mle_name
                                                                    (["Pulse";
                                                                    "Lib";
                                                                    "Reference"],
                                                                    "alloc"))
                                                                    [initializer2])])
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___4)))
                                                                    uu___3)))
                                                          uu___3))
                                            | Pulse_Syntax_Base.Tm_WithLocalArray
                                                {
                                                  Pulse_Syntax_Base.binder3 =
                                                    binder;
                                                  Pulse_Syntax_Base.initializer2
                                                    = initializer1;
                                                  Pulse_Syntax_Base.length =
                                                    length;
                                                  Pulse_Syntax_Base.body5 =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (633))
                                                              (Prims.of_int (26))
                                                              (Prims.of_int (633))
                                                              (Prims.of_int (54)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (633))
                                                              (Prims.of_int (57))
                                                              (Prims.of_int (646))
                                                              (Prims.of_int (47)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g
                                                           initializer1))
                                                     (fun uu___3 ->
                                                        (fun initializer2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (44)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (646))
                                                                    (Prims.of_int (47)))))
                                                                (Obj.magic
                                                                   (term_as_mlexpr
                                                                    g length))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    length1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (646))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (extend_env
                                                                    g
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_ty);
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_ppname)
                                                                    }))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    mlident,
                                                                    mlty,
                                                                    name1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (646))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (646))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___6)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_let
                                                                    (Pulse_Extract_CompilerLib.mk_mlletbinding
                                                                    false
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mut_mllb
                                                                    mlident
                                                                    ([],
                                                                    mlty)
                                                                    (Pulse_Extract_CompilerLib.mle_app
                                                                    (Pulse_Extract_CompilerLib.mle_name
                                                                    (["Pulse";
                                                                    "Lib";
                                                                    "Array";
                                                                    "Core"],
                                                                    "alloc"))
                                                                    [initializer2;
                                                                    length1])])
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                          uu___3))
                                            | Pulse_Syntax_Base.Tm_WithInv
                                                {
                                                  Pulse_Syntax_Base.name1 =
                                                    uu___3;
                                                  Pulse_Syntax_Base.body6 =
                                                    body;
                                                  Pulse_Syntax_Base.returns_inv
                                                    = uu___4;_}
                                                -> Obj.repr (extract g body)
                                            | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                {
                                                  Pulse_Syntax_Base.hint_type
                                                    = uu___3;
                                                  Pulse_Syntax_Base.binders =
                                                    uu___4;
                                                  Pulse_Syntax_Base.t3 = t;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_V2_Derived.fail
                                                     "Unexpected constructor: ProofHintWithBinders should have been desugared away")
                                            | Pulse_Syntax_Base.Tm_Admit
                                                uu___3 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        ((Pulse_Extract_CompilerLib.mle_app
                                                            (Pulse_Extract_CompilerLib.mle_tapp
                                                               (Pulse_Extract_CompilerLib.mle_name
                                                                  ([],
                                                                    "failwith"))
                                                               [Pulse_Extract_CompilerLib.mlty_unit])
                                                            [Pulse_Extract_CompilerLib.mle_unit]),
                                                          Pulse_Extract_CompilerLib.e_tag_impure))))))
                                   uu___1))) uu___))) uu___)
let rec (generalize :
  env ->
    FStar_Reflection_Types.typ ->
      Pulse_Syntax_Base.st_term FStar_Pervasives_Native.option ->
        ((env * Pulse_Extract_CompilerLib.mlident Prims.list *
           FStar_Reflection_Types.typ * Pulse_Syntax_Base.st_term
           FStar_Pervasives_Native.option),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (663)) (Prims.of_int (2))
                   (Prims.of_int (663)) (Prims.of_int (84)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (663)) (Prims.of_int (85))
                   (Prims.of_int (700)) (Prims.of_int (20)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (663)) (Prims.of_int (63))
                              (Prims.of_int (663)) (Prims.of_int (83)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string t))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             Prims.strcat "Generalizing arrow:\n"
                               (Prims.strcat uu___1 "\n"))))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (664)) (Prims.of_int (11))
                              (Prims.of_int (664)) (Prims.of_int (25)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (665)) (Prims.of_int (2))
                              (Prims.of_int (700)) (Prims.of_int (20)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           FStar_Reflection_V2_Builtins.inspect_ln t))
                     (fun uu___1 ->
                        (fun tv ->
                           match tv with
                           | FStar_Reflection_V2_Data.Tv_Arrow (b, c) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (667))
                                                (Prims.of_int (25))
                                                (Prims.of_int (667))
                                                (Prims.of_int (43)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (666))
                                                (Prims.of_int (21))
                                                (Prims.of_int (698))
                                                (Prims.of_int (20)))))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             FStar_Reflection_V2_Builtins.inspect_binder
                                               b))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             match uu___1 with
                                             | {
                                                 FStar_Reflection_V2_Data.sort2
                                                   = sort;
                                                 FStar_Reflection_V2_Data.qual
                                                   = uu___2;
                                                 FStar_Reflection_V2_Data.attrs
                                                   = uu___3;
                                                 FStar_Reflection_V2_Data.ppname2
                                                   = ppname;_}
                                                 ->
                                                 if
                                                   FStar_Reflection_V2_Data.uu___is_Tv_Unknown
                                                     (FStar_Reflection_V2_Builtins.inspect_ln
                                                        sort)
                                                 then
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.raise
                                                           (Extraction_failure
                                                              "Unexpected unknown sort when generalizing")))
                                                 else
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (37)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (20)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___5 ->
                                                                 Pulse_Extract_CompilerLib.is_type
                                                                   g.uenv_inner
                                                                   sort))
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 if uu___5
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V2_Builtins.inspect_comp
                                                                    c))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    cview ->
                                                                    match cview
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Data.C_Total
                                                                    t1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g.coreenv))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Var
                                                                    (FStar_Reflection_V2_Builtins.pack_namedv
                                                                    {
                                                                    FStar_Reflection_V2_Data.uniq
                                                                    = x;
                                                                    FStar_Reflection_V2_Data.sort
                                                                    =
                                                                    FStar_Reflection_Typing.sort_default;
                                                                    FStar_Reflection_V2_Data.ppname
                                                                    = ppname
                                                                    }))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun xt
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V2_Builtins.subst_term
                                                                    [
                                                                    FStar_Syntax_Syntax.DT
                                                                    (Prims.int_zero,
                                                                    xt)] t1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match e
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b1;
                                                                    Pulse_Syntax_Base.q
                                                                    = uu___7;
                                                                    Pulse_Syntax_Base.ascription
                                                                    = uu___8;
                                                                    Pulse_Syntax_Base.body
                                                                    = body;_};
                                                                    Pulse_Syntax_Base.range2
                                                                    = uu___9;
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    = uu___10;_}
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    (Pulse_Syntax_Base.tm_fstar
                                                                    xt
                                                                    FStar_Range.range_0))])
                                                                    | 
                                                                    uu___7 ->
                                                                    e))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun e1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (682))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V2_Builtins.pack_namedv
                                                                    {
                                                                    FStar_Reflection_V2_Data.uniq
                                                                    = x;
                                                                    FStar_Reflection_V2_Data.sort
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    sort);
                                                                    FStar_Reflection_V2_Data.ppname
                                                                    = ppname
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    namedv ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Extract_CompilerLib.extend_ty
                                                                    g.uenv_inner
                                                                    namedv))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun uenv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g.coreenv
                                                                    x
                                                                    (Pulse_Syntax_Base.mk_ppname
                                                                    ppname
                                                                    FStar_Range.range_0)
                                                                    (Pulse_Syntax_Base.tm_fstar
                                                                    sort
                                                                    FStar_Range.range_0)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    coreenv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    {
                                                                    uenv_inner
                                                                    = uenv;
                                                                    coreenv
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun g1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (generalize
                                                                    g1 t2 e1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (g2, tys,
                                                                    t3, e2)
                                                                    ->
                                                                    (g2,
                                                                    ((Pulse_Extract_CompilerLib.lookup_ty
                                                                    g2.uenv_inner
                                                                    namedv)
                                                                    :: tys),
                                                                    t3, e2)))))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    | 
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.raise
                                                                    (Extraction_failure
                                                                    "Unexpected effectful arrow"))))
                                                                    uu___6)))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (g, [],
                                                                    t, e)))))
                                                                uu___5))))
                                            uu___1)))
                           | uu___1 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> (g, [], t, e)))))
                          uu___1))) uu___)
let (debug_ :
  env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  = debug
let rec find_map :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives_Native.None
      | hd::tl ->
          let x = f hd in
          if FStar_Pervasives_Native.uu___is_Some x then x else find_map f tl
let (is_recursive :
  env ->
    FStar_Reflection_Types.fv ->
      FStar_Reflection_Types.sigelt ->
        (Prims.string FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun knot_name ->
      fun selt ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (711)) (Prims.of_int (16))
                   (Prims.of_int (711)) (Prims.of_int (38)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (711)) (Prims.of_int (41))
                   (Prims.of_int (733)) (Prims.of_int (39)))))
          (Obj.magic (Pulse_RuntimeUtils.get_attributes selt))
          (fun attrs ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  find_map
                    (fun t ->
                       match FStar_Reflection_V2_Builtins.inspect_ln t with
                       | FStar_Reflection_V2_Data.Tv_App (uu___1, uu___2) ->
                           (match FStar_Reflection_V2_Derived.collect_app_ln
                                    t
                            with
                            | (hd, args) ->
                                if
                                  FStar_Reflection_V2_Derived.is_fvar hd
                                    "FStar.Pervasives.Native.Mktuple2"
                                then
                                  (match args with
                                   | uu___3::uu___4::(tag, uu___5)::(value,
                                                                    uu___6)::[]
                                       ->
                                       (match ((match FStar_Reflection_V2_Builtins.inspect_ln
                                                        tag
                                                with
                                                | FStar_Reflection_V2_Data.Tv_Const
                                                    (FStar_Reflection_V2_Data.C_String
                                                    s) ->
                                                    FStar_Pervasives_Native.Some
                                                      s
                                                | uu___7 ->
                                                    FStar_Pervasives_Native.None),
                                                (match FStar_Reflection_V2_Builtins.inspect_ln
                                                         value
                                                 with
                                                 | FStar_Reflection_V2_Data.Tv_Const
                                                     (FStar_Reflection_V2_Data.C_String
                                                     s) ->
                                                     FStar_Pervasives_Native.Some
                                                       s
                                                 | uu___7 ->
                                                     FStar_Pervasives_Native.None))
                                        with
                                        | (FStar_Pervasives_Native.Some
                                           "pulse.recursive.knot",
                                           FStar_Pervasives_Native.Some v) ->
                                            FStar_Pervasives_Native.Some v
                                        | uu___7 ->
                                            FStar_Pervasives_Native.None)
                                   | uu___3 -> FStar_Pervasives_Native.None)
                                else FStar_Pervasives_Native.None)
                       | uu___1 -> FStar_Pervasives_Native.None) attrs))
let rec (extract_recursive :
  env ->
    Pulse_Syntax_Base.st_term ->
      FStar_Reflection_Types.fv ->
        ((Pulse_Extract_CompilerLib.mlexpr * Pulse_Extract_CompilerLib.e_tag),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun p ->
             fun rec_name ->
               match p.Pulse_Syntax_Base.term1 with
               | Pulse_Syntax_Base.Tm_Abs
                   { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                     Pulse_Syntax_Base.ascription = uu___;
                     Pulse_Syntax_Base.body = body;_}
                   ->
                   Obj.magic
                     (Obj.repr
                        (match body.Pulse_Syntax_Base.term1 with
                         | Pulse_Syntax_Base.Tm_Abs uu___1 ->
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (741))
                                        (Prims.of_int (37))
                                        (Prims.of_int (741))
                                        (Prims.of_int (51)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (740))
                                        (Prims.of_int (19))
                                        (Prims.of_int (745))
                                        (Prims.of_int (23)))))
                               (Obj.magic (extend_env g b))
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     match uu___2 with
                                     | (g1, mlident, mlty, name1) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Extract.Main.fst"
                                                       (Prims.of_int (742))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (742))
                                                       (Prims.of_int (47)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Extract.Main.fst"
                                                       (Prims.of_int (742))
                                                       (Prims.of_int (50))
                                                       (Prims.of_int (745))
                                                       (Prims.of_int (23)))))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                      body name1))
                                              (fun uu___3 ->
                                                 (fun body1 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (743))
                                                                  (Prims.of_int (22))
                                                                  (Prims.of_int (743))
                                                                  (Prims.of_int (55)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (742))
                                                                  (Prims.of_int (50))
                                                                  (Prims.of_int (745))
                                                                  (Prims.of_int (23)))))
                                                         (Obj.magic
                                                            (extract_recursive
                                                               g1 body1
                                                               rec_name))
                                                         (fun uu___3 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___4 ->
                                                                 match uu___3
                                                                 with
                                                                 | (body2,
                                                                    uu___5)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    (mlident,
                                                                    mlty)]
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_pure)))))
                                                   uu___3))) uu___2)
                         | uu___1 ->
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (747))
                                        (Prims.of_int (19))
                                        (Prims.of_int (747))
                                        (Prims.of_int (106)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (747))
                                        (Prims.of_int (109))
                                        (Prims.of_int (749))
                                        (Prims.of_int (17)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     Pulse_Syntax_Naming.subst_st_term body
                                       [Pulse_Syntax_Naming.DT
                                          (Prims.int_zero,
                                            (Pulse_Syntax_Base.tm_fstar
                                               (FStar_Reflection_V2_Builtins.pack_ln
                                                  (FStar_Reflection_V2_Data.Tv_FVar
                                                     rec_name))
                                               FStar_Range.range_0))]))
                               (fun uu___2 ->
                                  (fun body1 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (748))
                                                   (Prims.of_int (24))
                                                   (Prims.of_int (748))
                                                   (Prims.of_int (38)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (747))
                                                   (Prims.of_int (109))
                                                   (Prims.of_int (749))
                                                   (Prims.of_int (17)))))
                                          (Obj.magic (extract g body1))
                                          (fun uu___2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  match uu___2 with
                                                  | (body2, tag) ->
                                                      (body2, tag))))) uu___2)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_V2_Derived.fail
                           "Unexpected recursive definition of non-function")))
          uu___2 uu___1 uu___
let extract_recursive_knot :
  'uuuuu .
    env ->
      Pulse_Syntax_Base.st_term ->
        FStar_Reflection_Types.fv ->
          FStar_Reflection_Types.term ->
            ((Pulse_Extract_CompilerLib.mlmodule1 Prims.list, 'uuuuu)
               FStar_Pervasives.either,
              unit) FStar_Tactics_Effect.tac_repr
  =
  fun g ->
    fun p ->
      fun knot_name ->
        fun knot_typ ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (756)) (Prims.of_int (33))
                     (Prims.of_int (756)) (Prims.of_int (63)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (755)) (Prims.of_int (63))
                     (Prims.of_int (769)) (Prims.of_int (29)))))
            (Obj.magic
               (generalize g knot_typ (FStar_Pervasives_Native.Some p)))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | (g1, tys, lb_typ, FStar_Pervasives_Native.Some p1) ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Extract.Main.fst"
                                    (Prims.of_int (757)) (Prims.of_int (15))
                                    (Prims.of_int (757)) (Prims.of_int (51)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Extract.Main.fst"
                                    (Prims.of_int (757)) (Prims.of_int (54))
                                    (Prims.of_int (769)) (Prims.of_int (29)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Pulse_Extract_CompilerLib.term_as_mlty
                                   g1.uenv_inner lb_typ))
                           (fun uu___1 ->
                              (fun mlty ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (758))
                                               (Prims.of_int (34))
                                               (Prims.of_int (758))
                                               (Prims.of_int (78)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (757))
                                               (Prims.of_int (54))
                                               (Prims.of_int (769))
                                               (Prims.of_int (29)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            Pulse_Extract_CompilerLib.extend_fv
                                              g1.uenv_inner knot_name
                                              (tys, mlty)))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            match uu___1 with
                                            | (uenv, _mli, _ml_binding) ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (759))
                                                              (Prims.of_int (14))
                                                              (Prims.of_int (759))
                                                              (Prims.of_int (38)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (759))
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (769))
                                                              (Prims.of_int (29)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           {
                                                             uenv_inner =
                                                               uenv;
                                                             coreenv =
                                                               (g1.coreenv)
                                                           }))
                                                     (fun uu___2 ->
                                                        (fun g2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (760))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (760))
                                                                    (Prims.of_int (49)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (759))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (769))
                                                                    (Prims.of_int (29)))))
                                                                (Obj.magic
                                                                   (extract_recursive
                                                                    g2 p1
                                                                    knot_name))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (tm, tag)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (761))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (765))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (767))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (769))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (762))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (762))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (763))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (765))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Reflection_V2_Builtins.inspect_fv
                                                                    knot_name))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun lids
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (763))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (764))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (765))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (765))
                                                                    (Prims.of_int (30)))))
                                                                    (if
                                                                    Prims.uu___is_Nil
                                                                    lids
                                                                    then
                                                                    FStar_Tactics_Effect.raise
                                                                    (Extraction_failure
                                                                    "Unexpected empty name")
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.last
                                                                    lids))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    fv_name
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (767))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (767))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (769))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (769))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (debug_
                                                                    g2
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Extracted term ("
                                                                    (Prims.strcat
                                                                    fv_name
                                                                    "): "))
                                                                    (Prims.strcat
                                                                    (Pulse_Extract_CompilerLib.mlexpr_to_string
                                                                    tm) "\n"))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Inl
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mlm_let
                                                                    true
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mllb
                                                                    fv_name
                                                                    (tys,
                                                                    mlty) tm]]))))
                                                                    uu___3)))
                                                                    uu___2)))
                                                          uu___2))) uu___1)))
                                uu___1))) uu___)
let (extract_pulse :
  Pulse_Extract_CompilerLib.uenv ->
    FStar_Reflection_Types.sigelt ->
      Pulse_Syntax_Base.st_term ->
        ((Pulse_Extract_CompilerLib.mlmodule, Prims.string)
           FStar_Pervasives.either,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun selt ->
      fun p ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (775)) (Prims.of_int (12))
                   (Prims.of_int (775)) (Prims.of_int (52)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (776)) (Prims.of_int (2))
                   (Prims.of_int (810)) (Prims.of_int (75)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                {
                  uenv_inner = g;
                  coreenv = (Pulse_Extract_CompilerLib.initial_core_env g)
                }))
          (fun uu___ ->
             (fun g1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (776)) (Prims.of_int (2))
                              (Prims.of_int (776)) (Prims.of_int (74)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (777)) (Prims.of_int (2))
                              (Prims.of_int (810)) (Prims.of_int (75)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Extract.Main.fst"
                                    (Prims.of_int (776)) (Prims.of_int (10))
                                    (Prims.of_int (776)) (Prims.of_int (74)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Extract.Main.fst"
                                    (Prims.of_int (776)) (Prims.of_int (2))
                                    (Prims.of_int (776)) (Prims.of_int (74)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Extract.Main.fst"
                                          (Prims.of_int (776))
                                          (Prims.of_int (52))
                                          (Prims.of_int (776))
                                          (Prims.of_int (73)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "prims.fst"
                                          (Prims.of_int (590))
                                          (Prims.of_int (19))
                                          (Prims.of_int (590))
                                          (Prims.of_int (31)))))
                                 (Obj.magic
                                    (Pulse_Syntax_Printer.st_term_to_string p))
                                 (fun uu___ ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 ->
                                         Prims.strcat "About to extract:\n"
                                           (Prims.strcat uu___ "\n")))))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_V2_Builtins.print uu___))
                                uu___)))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Extract.Main.fst"
                                         (Prims.of_int (777))
                                         (Prims.of_int (2))
                                         (Prims.of_int (777))
                                         (Prims.of_int (83)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Extract.Main.fst"
                                         (Prims.of_int (779))
                                         (Prims.of_int (2))
                                         (Prims.of_int (810))
                                         (Prims.of_int (75)))))
                                (Obj.magic
                                   (debug g1
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (777))
                                                    (Prims.of_int (61))
                                                    (Prims.of_int (777))
                                                    (Prims.of_int (82)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "prims.fst"
                                                    (Prims.of_int (590))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (590))
                                                    (Prims.of_int (31)))))
                                           (Obj.magic
                                              (Pulse_Syntax_Printer.st_term_to_string
                                                 p))
                                           (fun uu___2 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___3 ->
                                                   Prims.strcat
                                                     "About to extract:\n"
                                                     (Prims.strcat uu___2
                                                        "\n"))))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      Obj.magic
                                        (FStar_Tactics_V2_Derived.try_with
                                           (fun uu___2 ->
                                              match () with
                                              | () ->
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (780))
                                                             (Prims.of_int (22))
                                                             (Prims.of_int (780))
                                                             (Prims.of_int (43)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (781))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (805))
                                                             (Prims.of_int (59)))))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          FStar_Reflection_V2_Builtins.inspect_sigelt
                                                            selt))
                                                    (fun uu___3 ->
                                                       (fun sigelt_view ->
                                                          match sigelt_view
                                                          with
                                                          | FStar_Reflection_V2_Data.Sg_Let
                                                              (is_rec, lbs)
                                                              ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (if
                                                                    is_rec ||
                                                                    ((FStar_List_Tot_Base.length
                                                                    lbs) <>
                                                                    Prims.int_one)
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.raise
                                                                    (Extraction_failure
                                                                    "Extraction of recursive lets is not yet supported"))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (786))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (786))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (785))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (803))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Reflection_V2_Builtins.inspect_lb
                                                                    (FStar_List_Tot_Base.hd
                                                                    lbs)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Reflection_V2_Data.lb_fv
                                                                    = lb_fv;
                                                                    FStar_Reflection_V2_Data.lb_us
                                                                    = uu___5;
                                                                    FStar_Reflection_V2_Data.lb_typ
                                                                    = lb_typ;
                                                                    FStar_Reflection_V2_Data.lb_def
                                                                    = uu___6;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (787))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (787))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (787))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (802))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (is_recursive
                                                                    g1 lb_fv
                                                                    selt))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (extract_recursive_knot
                                                                    g1 p
                                                                    lb_fv
                                                                    lb_typ)
                                                                    | 
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (790))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (802))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (generalize
                                                                    g1 lb_typ
                                                                    (FStar_Pervasives_Native.Some
                                                                    p)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (g2, tys,
                                                                    lb_typ1,
                                                                    FStar_Pervasives_Native.Some
                                                                    p1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (792))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (792))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (792))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (802))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Extract_CompilerLib.term_as_mlty
                                                                    g2.uenv_inner
                                                                    lb_typ1))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun mlty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (793))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (793))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (794))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (802))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.inspect_fv
                                                                    lb_fv))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    fv_name
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (794))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (795))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (795))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (802))
                                                                    (Prims.of_int (36)))))
                                                                    (if
                                                                    Prims.uu___is_Nil
                                                                    fv_name
                                                                    then
                                                                    FStar_Tactics_Effect.raise
                                                                    (Extraction_failure
                                                                    "Unexpected empty name")
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> ()))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (802))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g2 p1))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun p2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (802))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (simplify_st_term
                                                                    g2 p2))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun p3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (798))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (798))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (802))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g2 p3))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (tm, tag)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (799))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (799))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (802))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_List_Tot_Base.last
                                                                    fv_name))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    fv_name1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (802))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (802))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (debug_
                                                                    g2
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Extracted term ("
                                                                    (Prims.strcat
                                                                    fv_name1
                                                                    "): "))
                                                                    (Prims.strcat
                                                                    (Pulse_Extract_CompilerLib.mlexpr_to_string
                                                                    tm) "\n"))))
                                                                    uu___12)))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pervasives.Inl
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mlm_let
                                                                    false
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mllb
                                                                    fv_name1
                                                                    (tys,
                                                                    mlty) tm]]))))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___10)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___7)))
                                                                    uu___4))))
                                                          | uu___3 ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.raise
                                                                    (Extraction_failure
                                                                    "Unexpected sigelt"))))
                                                         uu___3))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         match uu___2 with
                                                         | Extraction_failure
                                                             msg ->
                                                             FStar_Pervasives.Inr
                                                               msg
                                                         | e ->
                                                             FStar_Pervasives.Inr
                                                               (Prims.strcat
                                                                  "Unexpected extraction error: "
                                                                  (Prims.strcat
                                                                    (Pulse_RuntimeUtils.print_exn
                                                                    e) "")))))
                                                uu___2))) uu___1))) uu___)))
               uu___)
let (extract_pulse_sig :
  Pulse_Extract_CompilerLib.uenv ->
    FStar_Reflection_Types.sigelt ->
      Pulse_Syntax_Base.st_term ->
        (((Pulse_Extract_CompilerLib.uenv * Pulse_Extract_CompilerLib.iface),
           Prims.string) FStar_Pervasives.either,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun selt ->
      fun p ->
        FStar_Tactics_V2_Derived.try_with
          (fun uu___ ->
             match () with
             | () ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (817)) (Prims.of_int (22))
                            (Prims.of_int (817)) (Prims.of_int (43)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (818)) (Prims.of_int (4))
                            (Prims.of_int (831)) (Prims.of_int (59)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 ->
                         FStar_Reflection_V2_Builtins.inspect_sigelt selt))
                   (fun uu___1 ->
                      (fun sigelt_view ->
                         match sigelt_view with
                         | FStar_Reflection_V2_Data.Sg_Let (is_rec, lbs) ->
                             Obj.magic
                               (Obj.repr
                                  (if
                                     is_rec ||
                                       ((FStar_List_Tot_Base.length lbs) <>
                                          Prims.int_one)
                                   then
                                     Obj.repr
                                       (FStar_Tactics_Effect.raise
                                          (Extraction_failure
                                             "Extraction of iface for recursive lets is not yet supported"))
                                   else
                                     Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (823))
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (823))
                                                   (Prims.of_int (60)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (822))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (830))
                                                   (Prims.of_int (49)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                FStar_Reflection_V2_Builtins.inspect_lb
                                                  (FStar_List_Tot_Base.hd lbs)))
                                          (fun uu___2 ->
                                             (fun uu___2 ->
                                                match uu___2 with
                                                | {
                                                    FStar_Reflection_V2_Data.lb_fv
                                                      = lb_fv;
                                                    FStar_Reflection_V2_Data.lb_us
                                                      = uu___3;
                                                    FStar_Reflection_V2_Data.lb_typ
                                                      = lb_typ;
                                                    FStar_Reflection_V2_Data.lb_def
                                                      = uu___4;_}
                                                    ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (824))
                                                                  (Prims.of_int (17))
                                                                  (Prims.of_int (824))
                                                                  (Prims.of_int (18)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (824))
                                                                  (Prims.of_int (21))
                                                                  (Prims.of_int (830))
                                                                  (Prims.of_int (49)))))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___5 -> g))
                                                         (fun uu___5 ->
                                                            (fun g0 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (825))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (825))
                                                                    (Prims.of_int (58)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (825))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (830))
                                                                    (Prims.of_int (49)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    uenv_inner
                                                                    = g;
                                                                    coreenv =
                                                                    (Pulse_Extract_CompilerLib.initial_core_env
                                                                    g)
                                                                    }))
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    (fun g1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (825))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (830))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (generalize
                                                                    g1 lb_typ
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (g2, tys,
                                                                    lb_typ1,
                                                                    uu___6)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (827))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (827))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (828))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (830))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (debug_
                                                                    g2
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (827))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (827))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    lb_typ1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Extracting ml typ: "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match 
                                                                    Pulse_Extract_CompilerLib.extend_fv
                                                                    g0 lb_fv
                                                                    (tys,
                                                                    (Pulse_Extract_CompilerLib.term_as_mlty
                                                                    g2.uenv_inner
                                                                    lb_typ1))
                                                                    with
                                                                    | 
                                                                    (g3,
                                                                    uu___9,
                                                                    e_bnd) ->
                                                                    FStar_Pervasives.Inl
                                                                    (g3,
                                                                    (Pulse_Extract_CompilerLib.iface_of_bindings
                                                                    [
                                                                    (lb_fv,
                                                                    e_bnd)]))))))
                                                                    uu___5)))
                                                                    uu___5)))
                                                              uu___5)))
                                               uu___2))))
                         | uu___1 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.raise
                                     (Extraction_failure "Unexpected sigelt"))))
                        uu___1))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        match uu___ with
                        | Extraction_failure msg -> FStar_Pervasives.Inr msg
                        | e ->
                            FStar_Pervasives.Inr
                              (Prims.strcat
                                 "Unexpected extraction error (iface): "
                                 (Prims.strcat
                                    (Pulse_RuntimeUtils.print_exn e) "")))))
               uu___)