open Prims
let (terms_to_string :
  Pulse_Syntax_Base.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (36))
               (Prims.of_int (23)) (Prims.of_int (36)) (Prims.of_int (68)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (36))
               (Prims.of_int (4)) (Prims.of_int (36)) (Prims.of_int (68)))))
      (Obj.magic
         (FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_String.concat "\n" uu___))
let (has_pure_vprops : Pulse_Syntax_Base.term -> Prims.bool) =
  fun pre ->
    FStar_List_Tot_Base.existsb Pulse_Syntax_Base.uu___is_Tm_Pure
      (Pulse_Checker_VPropEquiv.vprop_as_list pre)
let (elim_pure_explicit_lid : Prims.string Prims.list) =
  Pulse_Reflection_Util.mk_steel_wrapper_lid "elim_pure_explicit"
let (default_binder_annot : Pulse_Syntax_Base.binder) =
  {
    Pulse_Syntax_Base.binder_ty = Pulse_Syntax_Base.Tm_Unknown;
    Pulse_Syntax_Base.binder_ppname = Pulse_Syntax_Base.ppname_default
  }
let (add_intro_pure :
  Pulse_Syntax_Base.range ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term)
  =
  fun rng ->
    fun continuation ->
      fun p ->
        let wr t =
          { Pulse_Syntax_Base.term1 = t; Pulse_Syntax_Base.range1 = rng } in
        let intro_pure_tm =
          wr
            (Pulse_Syntax_Base.Tm_Protect
               {
                 Pulse_Syntax_Base.t =
                   (wr
                      (Pulse_Syntax_Base.Tm_IntroPure
                         {
                           Pulse_Syntax_Base.p = p;
                           Pulse_Syntax_Base.should_check =
                             Pulse_Syntax_Base.should_check_false
                         }))
               }) in
        wr
          (Pulse_Syntax_Base.Tm_Protect
             {
               Pulse_Syntax_Base.t =
                 (wr
                    (Pulse_Syntax_Base.Tm_Bind
                       {
                         Pulse_Syntax_Base.binder = default_binder_annot;
                         Pulse_Syntax_Base.head1 = intro_pure_tm;
                         Pulse_Syntax_Base.body1 = continuation
                       }))
             })
type uvar_tys =
  (Pulse_Checker_Inference.uvar * Pulse_Syntax_Base.term) Prims.list
let rec (prepare_instantiations :
  (Pulse_Syntax_Base.vprop * (Pulse_Syntax_Base.term, Pulse_Syntax_Base.term)
    FStar_Pervasives.either) Prims.list ->
    uvar_tys ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term Prims.list ->
          ((Pulse_Syntax_Base.vprop * (Pulse_Syntax_Base.vprop *
             (Pulse_Syntax_Base.term, Pulse_Syntax_Base.term)
             FStar_Pervasives.either) Prims.list * uvar_tys),
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun out ->
             fun out_uvars ->
               fun goal_vprop ->
                 fun witnesses ->
                   match (witnesses, goal_vprop) with
                   | ([], Pulse_Syntax_Base.Tm_ExistsSL (u, b, p)) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (70))
                                        (Prims.of_int (37))
                                        (Prims.of_int (72))
                                        (Prims.of_int (37)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (69))
                                        (Prims.of_int (30))
                                        (Prims.of_int (74))
                                        (Prims.of_int (103)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.fst"
                                              (Prims.of_int (71))
                                              (Prims.of_int (22))
                                              (Prims.of_int (71))
                                              (Prims.of_int (70)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.fst"
                                              (Prims.of_int (70))
                                              (Prims.of_int (37))
                                              (Prims.of_int (72))
                                              (Prims.of_int (37)))))
                                     (Obj.magic
                                        (Pulse_Checker_Inference.gen_uvar
                                           b.Pulse_Syntax_Base.binder_ppname))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             match uu___ with
                                             | (uv, t) ->
                                                 ((Pulse_Syntax_Naming.open_term'
                                                     p t Prims.int_zero),
                                                   (FStar_Pervasives.Inr t),
                                                   uv)))))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     match uu___ with
                                     | (next_goal_vprop, inst, uv) ->
                                         Obj.magic
                                           (prepare_instantiations
                                              ((goal_vprop, inst) :: out)
                                              ((uv,
                                                 (b.Pulse_Syntax_Base.binder_ty))
                                              :: out_uvars) next_goal_vprop
                                              [])) uu___)))
                   | ([], uu___) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> (goal_vprop, out, out_uvars))))
                   | (t::witnesses1, Pulse_Syntax_Base.Tm_ExistsSL (u, b, p))
                       ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (81))
                                        (Prims.of_int (10))
                                        (Prims.of_int (86))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (79))
                                        (Prims.of_int (42))
                                        (Prims.of_int (88))
                                        (Prims.of_int (96)))))
                               (match t with
                                | Pulse_Syntax_Base.Tm_Unknown ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (83))
                                                     (Prims.of_int (24))
                                                     (Prims.of_int (83))
                                                     (Prims.of_int (72)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (82))
                                                     (Prims.of_int (25))
                                                     (Prims.of_int (84))
                                                     (Prims.of_int (55)))))
                                            (Obj.magic
                                               (Pulse_Checker_Inference.gen_uvar
                                                  b.Pulse_Syntax_Base.binder_ppname))
                                            (fun uu___ ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    match uu___ with
                                                    | (uv, t1) ->
                                                        ((Pulse_Syntax_Naming.open_term'
                                                            p t1
                                                            Prims.int_zero),
                                                          (FStar_Pervasives.Inr
                                                             t1),
                                                          [(uv,
                                                             (b.Pulse_Syntax_Base.binder_ty))])))))
                                | uu___ ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___1 ->
                                               ((Pulse_Syntax_Naming.open_term'
                                                   p t Prims.int_zero),
                                                 (FStar_Pervasives.Inl t),
                                                 [])))))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     match uu___ with
                                     | (next_goal_vprop, inst, uvs) ->
                                         Obj.magic
                                           (prepare_instantiations
                                              ((goal_vprop, inst) :: out)
                                              (FStar_List_Tot_Base.op_At uvs
                                                 out_uvars) next_goal_vprop
                                              witnesses1)) uu___)))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_V2_Derived.fail
                               "Unexpected number of instantiations in intro")))
            uu___3 uu___2 uu___1 uu___
let rec (build_instantiations :
  Pulse_Checker_Inference.solution ->
    (Pulse_Syntax_Base.term * (Pulse_Syntax_Base.term,
      Pulse_Syntax_Base.term) FStar_Pervasives.either) Prims.list ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun solutions ->
    fun insts ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (95))
                 (Prims.of_int (29)) (Prims.of_int (107))
                 (Prims.of_int (102)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (109))
                 (Prims.of_int (8)) (Prims.of_int (116)) (Prims.of_int (92)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun uu___1 ->
                match uu___1 with
                | (v, i) ->
                    (match i with
                     | FStar_Pervasives.Inl user_provided ->
                         Pulse_Typing.wr
                           (Pulse_Syntax_Base.Tm_IntroExists
                              {
                                Pulse_Syntax_Base.erased = false;
                                Pulse_Syntax_Base.p2 =
                                  (Pulse_Checker_Inference.apply_solution
                                     solutions v);
                                Pulse_Syntax_Base.witnesses = [user_provided];
                                Pulse_Syntax_Base.should_check1 =
                                  Pulse_Syntax_Base.should_check_true
                              })
                     | FStar_Pervasives.Inr inferred ->
                         (match Pulse_Syntax_Pure.unreveal
                                  (Pulse_Checker_Inference.apply_solution
                                     solutions inferred)
                          with
                          | FStar_Pervasives_Native.Some sol ->
                              Pulse_Typing.wr
                                (Pulse_Syntax_Base.Tm_IntroExists
                                   {
                                     Pulse_Syntax_Base.erased = true;
                                     Pulse_Syntax_Base.p2 =
                                       (Pulse_Checker_Inference.apply_solution
                                          solutions v);
                                     Pulse_Syntax_Base.witnesses = [sol];
                                     Pulse_Syntax_Base.should_check1 =
                                       Pulse_Syntax_Base.should_check_false
                                   })
                          | uu___2 ->
                              Pulse_Typing.wr
                                (Pulse_Syntax_Base.Tm_IntroExists
                                   {
                                     Pulse_Syntax_Base.erased = true;
                                     Pulse_Syntax_Base.p2 =
                                       (Pulse_Checker_Inference.apply_solution
                                          solutions v);
                                     Pulse_Syntax_Base.witnesses =
                                       [Pulse_Checker_Inference.apply_solution
                                          solutions inferred];
                                     Pulse_Syntax_Base.should_check1 =
                                       Pulse_Syntax_Base.should_check_false
                                   })))))
        (fun uu___ ->
           (fun one_inst ->
              match insts with
              | [] ->
                  Obj.magic
                    (Obj.repr (FStar_Tactics_V2_Derived.fail "Impossible"))
              | hd::[] ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             Pulse_Typing.wr
                               (Pulse_Syntax_Base.Tm_Protect
                                  { Pulse_Syntax_Base.t = (one_inst hd) }))))
              | hd::tl ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Checker.fst"
                                   (Prims.of_int (113)) (Prims.of_int (23))
                                   (Prims.of_int (116)) (Prims.of_int (92)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Checker.fst"
                                   (Prims.of_int (113)) (Prims.of_int (20))
                                   (Prims.of_int (116)) (Prims.of_int (92)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (114))
                                         (Prims.of_int (28))
                                         (Prims.of_int (116))
                                         (Prims.of_int (89)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (113))
                                         (Prims.of_int (23))
                                         (Prims.of_int (116))
                                         (Prims.of_int (92)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (114))
                                               (Prims.of_int (32))
                                               (Prims.of_int (116))
                                               (Prims.of_int (89)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (114))
                                               (Prims.of_int (28))
                                               (Prims.of_int (116))
                                               (Prims.of_int (89)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (114))
                                                     (Prims.of_int (35))
                                                     (Prims.of_int (116))
                                                     (Prims.of_int (89)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (114))
                                                     (Prims.of_int (32))
                                                     (Prims.of_int (116))
                                                     (Prims.of_int (89)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (114))
                                                           (Prims.of_int (46))
                                                           (Prims.of_int (116))
                                                           (Prims.of_int (86)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (114))
                                                           (Prims.of_int (35))
                                                           (Prims.of_int (116))
                                                           (Prims.of_int (89)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (116))
                                                                 (Prims.of_int (53))
                                                                 (Prims.of_int (116))
                                                                 (Prims.of_int (86)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (114))
                                                                 (Prims.of_int (46))
                                                                 (Prims.of_int (116))
                                                                 (Prims.of_int (86)))))
                                                        (Obj.magic
                                                           (build_instantiations
                                                              solutions tl))
                                                        (fun uu___ ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___1 ->
                                                                {
                                                                  Pulse_Syntax_Base.binder
                                                                    =
                                                                    default_binder_annot;
                                                                  Pulse_Syntax_Base.head1
                                                                    =
                                                                    (
                                                                    Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    (one_inst
                                                                    hd)
                                                                    }));
                                                                  Pulse_Syntax_Base.body1
                                                                    = uu___
                                                                }))))
                                                  (fun uu___ ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          Pulse_Syntax_Base.Tm_Bind
                                                            uu___))))
                                            (fun uu___ ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Pulse_Typing.wr uu___))))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              { Pulse_Syntax_Base.t = uu___ }))))
                                (fun uu___ ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        Pulse_Syntax_Base.Tm_Protect uu___))))
                          (fun uu___ ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> Pulse_Typing.wr uu___)))))
             uu___)
let (maybe_infer_intro_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun st ->
      fun pre ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (123)) (Prims.of_int (33))
                   (Prims.of_int (135)) (Prims.of_int (18)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (140)) (Prims.of_int (4))
                   (Prims.of_int (228)) (Prims.of_int (10)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun t ->
                  match FStar_List_Tot_Base.partition
                          (fun uu___1 ->
                             match uu___1 with
                             | Pulse_Syntax_Base.Tm_Pure uu___2 -> false
                             | Pulse_Syntax_Base.Tm_Emp -> false
                             | uu___2 -> true)
                          (Pulse_Checker_VPropEquiv.vprop_as_list t)
                  with
                  | (rest, pure) ->
                      (((match Pulse_Checker_VPropEquiv.list_as_vprop rest
                         with
                         | Pulse_Syntax_Base.Tm_Star
                             (t1, Pulse_Syntax_Base.Tm_Emp) -> t1
                         | Pulse_Syntax_Base.Tm_Star
                             (Pulse_Syntax_Base.Tm_Emp, t1) -> t1
                         | t1 -> t1)), pure)))
          (fun uu___ ->
             (fun remove_pure_conjuncts ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (140)) (Prims.of_int (4))
                              (Prims.of_int (145)) (Prims.of_int (5)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (145)) (Prims.of_int (6))
                              (Prims.of_int (228)) (Prims.of_int (10)))))
                     (if Pulse_RuntimeUtils.debug_at_level g "inference"
                      then
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (142))
                                         (Prims.of_int (14))
                                         (Prims.of_int (144))
                                         (Prims.of_int (43)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (141))
                                         (Prims.of_int (9))
                                         (Prims.of_int (145))
                                         (Prims.of_int (5)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (144))
                                               (Prims.of_int (18))
                                               (Prims.of_int (144))
                                               (Prims.of_int (42)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (142))
                                               (Prims.of_int (14))
                                               (Prims.of_int (144))
                                               (Prims.of_int (43)))))
                                      (Obj.magic
                                         (Pulse_Syntax_Printer.st_term_to_string
                                            st))
                                      (fun uu___ ->
                                         (fun uu___ ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (142))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (144))
                                                          (Prims.of_int (43)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (142))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (144))
                                                          (Prims.of_int (43)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (143))
                                                                (Prims.of_int (18))
                                                                (Prims.of_int (143))
                                                                (Prims.of_int (46)))))
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
                                                             st.Pulse_Syntax_Base.range1))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               fun x ->
                                                                 Prims.strcat
                                                                   (Prims.strcat
                                                                    "At "
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    ": infer_intro_exists for "))
                                                                   (Prims.strcat
                                                                    x "\n")))))
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
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (146))
                                         (Prims.of_int (50))
                                         (Prims.of_int (146))
                                         (Prims.of_int (57)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (145))
                                         (Prims.of_int (6))
                                         (Prims.of_int (228))
                                         (Prims.of_int (10)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 -> st.Pulse_Syntax_Base.term1))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      match uu___1 with
                                      | Pulse_Syntax_Base.Tm_IntroExists
                                          {
                                            Pulse_Syntax_Base.erased = erased;
                                            Pulse_Syntax_Base.p2 = t;
                                            Pulse_Syntax_Base.witnesses =
                                              witnesses;
                                            Pulse_Syntax_Base.should_check1 =
                                              uu___2;_}
                                          ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.fst"
                                                        (Prims.of_int (147))
                                                        (Prims.of_int (15))
                                                        (Prims.of_int (147))
                                                        (Prims.of_int (64)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.fst"
                                                        (Prims.of_int (146))
                                                        (Prims.of_int (60))
                                                        (Prims.of_int (228))
                                                        (Prims.of_int (10)))))
                                               (Obj.magic
                                                  (Pulse_Checker_Pure.instantiate_term_implicits
                                                     g t))
                                               (fun uu___3 ->
                                                  (fun uu___3 ->
                                                     match uu___3 with
                                                     | (t1, uu___4) ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (73)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                              (Obj.magic
                                                                 (prepare_instantiations
                                                                    [] [] t1
                                                                    witnesses))
                                                              (fun uu___5 ->
                                                                 (fun uu___5
                                                                    ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (goal_vprop,
                                                                    insts,
                                                                    uvs) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    remove_pure_conjuncts
                                                                    goal_vprop))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (goal_vprop1,
                                                                    pure_conjuncts)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.try_inst_uvs_in_goal
                                                                    pre
                                                                    goal_vprop1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    solutions
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun
                                                                    solutions1
                                                                    ->
                                                                    fun p ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    p))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun p1
                                                                    ->
                                                                    match p1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    p2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.try_solve_pure_equalities
                                                                    p2))
                                                                    (fun sols
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    sols
                                                                    solutions1))))
                                                                    | 
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    solutions1))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    maybe_solve_pure
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.fold_left
                                                                    maybe_solve_pure
                                                                    solutions
                                                                    pure_conjuncts))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    solutions1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    g
                                                                    "inference"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (68)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.solutions_to_string
                                                                    solutions1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (68)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (61)))))
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
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pure_conjuncts)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "maybe_infer_intro_exists: solutions after solving pure conjuncts ("
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "): "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8
                                                                    uu___7))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___7))
                                                                    uu___7)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun
                                                                    ty_opt ->
                                                                    fun e ->
                                                                    match ty_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Pulse_Syntax_Pure.tm_pureapp
                                                                    (Pulse_Syntax_Pure.tm_fvar
                                                                    (Pulse_Syntax_Base.as_fv
                                                                    Pulse_Reflection_Util.hide_lid))
                                                                    FStar_Pervasives_Native.None
                                                                    e
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ty ->
                                                                    Pulse_Syntax_Pure.tm_pureapp
                                                                    (Pulse_Syntax_Pure.tm_pureapp
                                                                    (Pulse_Syntax_Pure.tm_fvar
                                                                    (Pulse_Syntax_Base.as_fv
                                                                    Pulse_Reflection_Util.hide_lid))
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit)
                                                                    ty)
                                                                    FStar_Pervasives_Native.None
                                                                    e))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    mk_hide
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun uv ->
                                                                    match 
                                                                    FStar_List_Tot_Base.tryFind
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (u,
                                                                    uu___10)
                                                                    ->
                                                                    Pulse_Checker_Inference.uvar_eq
                                                                    u uv) uvs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (uu___9,
                                                                    ty) ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ty))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    type_of_uvar
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (u, v) ->
                                                                    (match 
                                                                    Pulse_Syntax_Pure.unreveal
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___10
                                                                    ->
                                                                    (u,
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    (u,
                                                                    (mk_hide
                                                                    (type_of_uvar
                                                                    u)
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v)))))
                                                                    solutions1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    solutions2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (match 
                                                                    FStar_List_Tot_Base.tryFind
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (u,
                                                                    _u_ty) ->
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    (Pulse_Checker_Inference.find_solution
                                                                    solutions2
                                                                    u)) uvs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (u,
                                                                    uu___8)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (98)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.range_to_string
                                                                    (Pulse_Checker_Inference.range_of_uvar
                                                                    u)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (98)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.uvar_to_string
                                                                    u))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Could not instantiate existential variable "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    " introduced at "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    uu___10
                                                                    uu___9))))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.print_context
                                                                    g))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    [uu___10]))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Issue.mk_issue
                                                                    "Error"
                                                                    uu___9
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.range1))
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_RuntimeUtils.error_code_uninstantiated_variable
                                                                    ()))
                                                                    uu___10))))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun i ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.log_issues
                                                                    [i]))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.uvar_to_string
                                                                    u))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    "maybe_infer_intro_exists: unification failed for uvar "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    "\n")))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun t2 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    = t2;
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1)
                                                                    }))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun wr
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (build_instantiations
                                                                    solutions2
                                                                    insts))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    intro_exists_chain
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_List_Tot_Base.collect
                                                                    (fun vp
                                                                    ->
                                                                    match 
                                                                    Pulse_Checker_Inference.apply_solution
                                                                    solutions2
                                                                    vp
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    p -> 
                                                                    [p]
                                                                    | 
                                                                    p -> [])
                                                                    pure_conjuncts))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    pure_conjuncts1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (111)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_List_Tot_Base.fold_left
                                                                    (add_intro_pure
                                                                    intro_exists_chain.Pulse_Syntax_Base.range1)
                                                                    intro_exists_chain
                                                                    pure_conjuncts1))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    result ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (14)))))
                                                                    (if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    g
                                                                    "inference"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (226))
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
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    result))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "Inferred pure and exists:{\n\t "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    "\n\t}")))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___9))
                                                                    uu___9)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> ()))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> result))))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                   uu___5)))
                                                    uu___3))) uu___1))) uu___)))
               uu___)
let (handle_framing_failure :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Checker_Common.post_hint_opt ->
            Pulse_Checker_Framing.framing_failure ->
              Pulse_Checker_Common.check_t ->
                ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun failure ->
              fun check ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (240)) (Prims.of_int (17))
                           (Prims.of_int (240)) (Prims.of_int (43)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (241)) (Prims.of_int (4))
                           (Prims.of_int (290)) (Prims.of_int (30)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        fun t ->
                          {
                            Pulse_Syntax_Base.term1 = t;
                            Pulse_Syntax_Base.range1 =
                              (t0.Pulse_Syntax_Base.range1)
                          }))
                  (fun uu___ ->
                     (fun wr ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (241)) (Prims.of_int (4))
                                      (Prims.of_int (249)) (Prims.of_int (5)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (249)) (Prims.of_int (6))
                                      (Prims.of_int (290))
                                      (Prims.of_int (30)))))
                             (if
                                Pulse_RuntimeUtils.debug_at_level g
                                  "inference"
                              then
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (243))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (248))
                                                 (Prims.of_int (66)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (242))
                                                 (Prims.of_int (9))
                                                 (Prims.of_int (249))
                                                 (Prims.of_int (5)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (248))
                                                       (Prims.of_int (22))
                                                       (Prims.of_int (248))
                                                       (Prims.of_int (65)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (243))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (248))
                                                       (Prims.of_int (66)))))
                                              (Obj.magic
                                                 (terms_to_string
                                                    failure.Pulse_Checker_Framing.remaining_context))
                                              (fun uu___ ->
                                                 (fun uu___ ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (243))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (248))
                                                                  (Prims.of_int (66)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (243))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (248))
                                                                  (Prims.of_int (66)))))
                                                         (Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (71)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (66)))))
                                                               (Obj.magic
                                                                  (terms_to_string
                                                                    failure.Pulse_Checker_Framing.unmatched_preconditions))
                                                               (fun uu___1 ->
                                                                  (fun uu___1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (46)))))
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
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (251))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (251))
                                                 (Prims.of_int (91)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (249))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (290))
                                                 (Prims.of_int (30)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              FStar_List_Tot_Base.partition
                                                (fun uu___2 ->
                                                   match uu___2 with
                                                   | Pulse_Syntax_Base.Tm_Pure
                                                       uu___3 -> true
                                                   | uu___3 -> false)
                                                failure.Pulse_Checker_Framing.unmatched_preconditions))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | (pures, rest) ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (254))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (260))
                                                                (Prims.of_int (13)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (261))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (290))
                                                                (Prims.of_int (30)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Util.fold_left
                                                             (fun uu___3 ->
                                                                fun uu___2 ->
                                                                  (fun t ->
                                                                    fun p ->
                                                                    match p
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    p1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    add_intro_pure
                                                                    t0.Pulse_Syntax_Base.range1
                                                                    t p1))
                                                                    | 
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Impossible"))
                                                                    uu___3
                                                                    uu___2)
                                                             (wr
                                                                (Pulse_Syntax_Base.Tm_Protect
                                                                   {
                                                                    Pulse_Syntax_Base.t
                                                                    = t0
                                                                   })) pures))
                                                       (fun uu___2 ->
                                                          (fun t ->
                                                             let rec handle_intro_exists
                                                               rest1 t1 =
                                                               match rest1
                                                               with
                                                               | [] ->
                                                                   check g t1
                                                                    pre ()
                                                                    post_hint
                                                               | (Pulse_Syntax_Base.Tm_ExistsSL
                                                                   (u, ty, p))::rest2
                                                                   ->
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (15)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    default_binder_annot;
                                                                    Pulse_Syntax_Base.head1
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = true;
                                                                    Pulse_Syntax_Base.p2
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p));
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = [];
                                                                    Pulse_Syntax_Base.should_check1
                                                                    =
                                                                    Pulse_Syntax_Base.should_check_true
                                                                    }))
                                                                    }));
                                                                    Pulse_Syntax_Base.body1
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    = t1
                                                                    }))
                                                                    }))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (handle_intro_exists
                                                                    rest2
                                                                    (wr t2)))
                                                                    uu___2)
                                                               | uu___2 ->
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    t0))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (terms_to_string
                                                                    failure.Pulse_Checker_Framing.remaining_context))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (286))
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
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    uu___3) in
                                                             Obj.magic
                                                               (handle_intro_exists
                                                                  rest t))
                                                            uu___2))) uu___1)))
                                  uu___))) uu___)
let (protect : Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term) =
  fun t ->
    {
      Pulse_Syntax_Base.term1 =
        (Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t });
      Pulse_Syntax_Base.range1 = (t.Pulse_Syntax_Base.range1)
    }
let rec (unprotect : Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term)
  =
  fun t ->
    let wr t0 =
      {
        Pulse_Syntax_Base.term1 = t0;
        Pulse_Syntax_Base.range1 = (t.Pulse_Syntax_Base.range1)
      } in
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Protect
        {
          Pulse_Syntax_Base.t =
            {
              Pulse_Syntax_Base.term1 = Pulse_Syntax_Base.Tm_Bind
                { Pulse_Syntax_Base.binder = binder;
                  Pulse_Syntax_Base.head1 = head;
                  Pulse_Syntax_Base.body1 = body;_};
              Pulse_Syntax_Base.range1 = uu___;_};_}
        ->
        wr
          (Pulse_Syntax_Base.Tm_Bind
             {
               Pulse_Syntax_Base.binder = binder;
               Pulse_Syntax_Base.head1 = (protect head);
               Pulse_Syntax_Base.body1 = body
             })
    | Pulse_Syntax_Base.Tm_Protect
        {
          Pulse_Syntax_Base.t =
            {
              Pulse_Syntax_Base.term1 = Pulse_Syntax_Base.Tm_If
                { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
                  Pulse_Syntax_Base.else_ = else_;
                  Pulse_Syntax_Base.post2 = post;_};
              Pulse_Syntax_Base.range1 = uu___;_};_}
        ->
        wr
          (Pulse_Syntax_Base.Tm_If
             {
               Pulse_Syntax_Base.b1 = b;
               Pulse_Syntax_Base.then_ = (protect then_);
               Pulse_Syntax_Base.else_ = (protect else_);
               Pulse_Syntax_Base.post2 = post
             })
    | Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t1;_} ->
        unprotect t1
    | uu___ -> t
let (elim_then_check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.st_term ->
          unit Pulse_Checker_Common.post_hint_opt ->
            Pulse_Checker_Common.check_t ->
              ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun st ->
          fun post_hint ->
            fun check ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (313)) (Prims.of_int (48))
                         (Prims.of_int (313)) (Prims.of_int (82)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (313)) (Prims.of_int (3))
                         (Prims.of_int (320)) (Prims.of_int (44)))))
                (Obj.magic
                   (Pulse_Checker_Auto_ElimExists.elim_exists g ctxt ()))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | FStar_Pervasives.Mkdtuple4
                          (g', ctxt', ctxt'_typing, elab_k) ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (314))
                                        (Prims.of_int (51))
                                        (Prims.of_int (314))
                                        (Prims.of_int (82)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (313))
                                        (Prims.of_int (85))
                                        (Prims.of_int (320))
                                        (Prims.of_int (44)))))
                               (Obj.magic
                                  (Pulse_Checker_Auto_ElimPure.elim_pure g'
                                     ctxt' ()))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | FStar_Pervasives.Mkdtuple4
                                         (g'', ctxt'', ctxt'_typing1,
                                          elab_k')
                                         ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (315))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (318))
                                                       (Prims.of_int (44)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (318))
                                                       (Prims.of_int (46))
                                                       (Prims.of_int (320))
                                                       (Prims.of_int (44)))))
                                              (if
                                                 Pulse_RuntimeUtils.debug_at_level
                                                   g "inference"
                                               then
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (316))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (318))
                                                                  (Prims.of_int (43)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (316))
                                                                  (Prims.of_int (9))
                                                                  (Prims.of_int (318))
                                                                  (Prims.of_int (44)))))
                                                         (Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (41)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (43)))))
                                                               (Obj.magic
                                                                  (Pulse_Syntax_Printer.term_to_string
                                                                    ctxt''))
                                                               (fun uu___2 ->
                                                                  (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (317))
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
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ctxt))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Eliminated context from\n\t"
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    "\n\tto "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_V2_Builtins.print
                                                                    uu___2))
                                                              uu___2)))
                                               else
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 -> ()))))
                                              (fun uu___2 ->
                                                 (fun uu___2 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (319))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (319))
                                                                  (Prims.of_int (66)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (320))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (320))
                                                                  (Prims.of_int (44)))))
                                                         (Obj.magic
                                                            (check g''
                                                               (protect st)
                                                               ctxt'' ()
                                                               post_hint))
                                                         (fun uu___3 ->
                                                            (fun res ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (44)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (44)))))
                                                                    (
                                                                    Obj.magic
                                                                    (elab_k'
                                                                    post_hint
                                                                    res))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (elab_k
                                                                    post_hint
                                                                    uu___3))
                                                                    uu___3)))
                                                              uu___3)))
                                                   uu___2))) uu___1))) uu___)
let rec (check' : Prims.bool -> Pulse_Checker_Common.check_t) =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              if
                Prims.op_Negation
                  (Pulse_Syntax_Base.uu___is_Tm_Protect
                     t.Pulse_Syntax_Base.term1)
              then elim_then_check g pre () t post_hint (check' allow_inst)
              else
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (341)) (Prims.of_int (4))
                           (Prims.of_int (346)) (Prims.of_int (5)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (346)) (Prims.of_int (6))
                           (Prims.of_int (424)) (Prims.of_int (20)))))
                  (if Pulse_RuntimeUtils.debug_at_level g "proof_states"
                   then
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (343))
                                      (Prims.of_int (14))
                                      (Prims.of_int (345))
                                      (Prims.of_int (51)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (342)) (Prims.of_int (9))
                                      (Prims.of_int (346)) (Prims.of_int (5)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.fst"
                                            (Prims.of_int (345))
                                            (Prims.of_int (28))
                                            (Prims.of_int (345))
                                            (Prims.of_int (50)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.fst"
                                            (Prims.of_int (343))
                                            (Prims.of_int (14))
                                            (Prims.of_int (345))
                                            (Prims.of_int (51)))))
                                   (Obj.magic
                                      (Pulse_Syntax_Printer.term_to_string
                                         pre))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (343))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (345))
                                                       (Prims.of_int (51)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (343))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (345))
                                                       (Prims.of_int (51)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.fst"
                                                             (Prims.of_int (344))
                                                             (Prims.of_int (28))
                                                             (Prims.of_int (344))
                                                             (Prims.of_int (55)))))
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
                                                          t.Pulse_Syntax_Base.range1))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            fun x ->
                                                              Prims.strcat
                                                                (Prims.strcat
                                                                   "At "
                                                                   (Prims.strcat
                                                                    uu___2
                                                                    ": context is {\n"))
                                                                (Prims.strcat
                                                                   x "\n}")))))
                                              (fun uu___2 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 ->
                                                      uu___2 uu___1))))
                                        uu___1)))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   Obj.magic
                                     (FStar_Tactics_V2_Builtins.print uu___1))
                                  uu___1)))
                   else
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> ()))))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (347))
                                      (Prims.of_int (12))
                                      (Prims.of_int (347))
                                      (Prims.of_int (23)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (347))
                                      (Prims.of_int (26))
                                      (Prims.of_int (424))
                                      (Prims.of_int (20)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> unprotect t))
                             (fun uu___2 ->
                                (fun t1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (348))
                                                 (Prims.of_int (12))
                                                 (Prims.of_int (348))
                                                 (Prims.of_int (47)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (349))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (424))
                                                 (Prims.of_int (20)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              Pulse_Checker_Pure.push_context
                                                (Pulse_Syntax_Printer.tag_of_st_term
                                                   t1) g))
                                        (fun uu___2 ->
                                           (fun g1 ->
                                              Obj.magic
                                                (FStar_Tactics_V2_Derived.try_with
                                                   (fun uu___2 ->
                                                      (fun uu___2 ->
                                                         match () with
                                                         | () ->
                                                             (match t1.Pulse_Syntax_Base.term1
                                                              with
                                                              | Pulse_Syntax_Base.Tm_Protect
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Protect should have been removed"))
                                                              | Pulse_Syntax_Base.Tm_Return
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_Return.check_return
                                                                    allow_inst
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint))
                                                              | Pulse_Syntax_Base.Tm_Abs
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_Abs.check_abs
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    (check'
                                                                    true)))
                                                              | Pulse_Syntax_Base.Tm_STApp
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_STApp.check_stapp
                                                                    allow_inst
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    check'))
                                                              | Pulse_Syntax_Base.Tm_Bind
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_Bind.check_bind
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    (check'
                                                                    true)))
                                                              | Pulse_Syntax_Base.Tm_TotBind
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_Bind.check_tot_bind
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    (check'
                                                                    true)))
                                                              | Pulse_Syntax_Base.Tm_If
                                                                  {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b;
                                                                    Pulse_Syntax_Base.then_
                                                                    = e1;
                                                                    Pulse_Syntax_Base.else_
                                                                    = e2;
                                                                    Pulse_Syntax_Base.post2
                                                                    = post_if;_}
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (60)))))
                                                                    (match 
                                                                    (post_if,
                                                                    post_hint)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.Some
                                                                    p) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    p)))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    p,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Common.intro_post_hint
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    p))
                                                                    | 
                                                                    (uu___3,
                                                                    uu___4)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Either two annotations for if post or none")))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_If.check_if
                                                                    g1 b e1
                                                                    e2 pre ()
                                                                    post
                                                                    (check'
                                                                    true)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t2, c,
                                                                    d) ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t2, c,
                                                                    d)))))
                                                                    uu___3)))
                                                              | Pulse_Syntax_Base.Tm_IntroPure
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_IntroPure.check_intro_pure
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint))
                                                              | Pulse_Syntax_Base.Tm_ElimExists
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_Exists.check_elim_exists
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint))
                                                              | Pulse_Syntax_Base.Tm_IntroExists
                                                                  {
                                                                    Pulse_Syntax_Base.erased
                                                                    = uu___3;
                                                                    Pulse_Syntax_Base.p2
                                                                    = uu___4;
                                                                    Pulse_Syntax_Base.witnesses
                                                                    =
                                                                    witnesses;
                                                                    Pulse_Syntax_Base.should_check1
                                                                    = uu___5;_}
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match witnesses
                                                                    with
                                                                    | 
                                                                    w::[] ->
                                                                    (match w
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Unknown
                                                                    -> true
                                                                    | 
                                                                    uu___7 ->
                                                                    false)
                                                                    | 
                                                                    uu___7 ->
                                                                    true))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    should_infer_witnesses
                                                                    ->
                                                                    if
                                                                    should_infer_witnesses
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (maybe_infer_intro_exists
                                                                    g1 t1 pre))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    unary_intros
                                                                    ->
                                                                    Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g1
                                                                    unary_intros
                                                                    pre ()
                                                                    post_hint))
                                                                    uu___6))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Checker_Exists.check_intro_exists_either
                                                                    g1 t1
                                                                    FStar_Pervasives_Native.None
                                                                    pre ()
                                                                    post_hint))
                                                                    uu___6)))
                                                              | Pulse_Syntax_Base.Tm_While
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_While.check_while
                                                                    allow_inst
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    check'))
                                                              | Pulse_Syntax_Base.Tm_Admit
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_Admit.check_admit
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint))
                                                              | Pulse_Syntax_Base.Tm_Par
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_Par.check_par
                                                                    allow_inst
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    check'))
                                                              | Pulse_Syntax_Base.Tm_WithLocal
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_WithLocal.check_withlocal
                                                                    allow_inst
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    check'))
                                                              | Pulse_Syntax_Base.Tm_Rewrite
                                                                  uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (Pulse_Checker_Rewrite.check_rewrite
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint))))
                                                        uu___2)
                                                   (fun uu___2 ->
                                                      (fun uu___2 ->
                                                         match uu___2 with
                                                         | Pulse_Checker_Common.Framing_failure
                                                             failure ->
                                                             Obj.magic
                                                               (Obj.repr
                                                                  (handle_framing_failure
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    failure
                                                                    (check'
                                                                    true)))
                                                         | e ->
                                                             Obj.magic
                                                               (Obj.repr
                                                                  (FStar_Tactics_Effect.raise
                                                                    e)))
                                                        uu___2))) uu___2)))
                                  uu___2))) uu___1)
let (check : Pulse_Checker_Common.check_t) = check' true