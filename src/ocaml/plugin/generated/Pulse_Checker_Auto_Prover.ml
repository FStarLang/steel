open Prims
type framing_failure =
  {
  unmatched_preconditions: Pulse_Syntax_Base.term Prims.list ;
  remaining_context: Pulse_Syntax_Base.term Prims.list }
let (__proj__Mkframing_failure__item__unmatched_preconditions :
  framing_failure -> Pulse_Syntax_Base.term Prims.list) =
  fun projectee ->
    match projectee with
    | { unmatched_preconditions; remaining_context;_} ->
        unmatched_preconditions
let (__proj__Mkframing_failure__item__remaining_context :
  framing_failure -> Pulse_Syntax_Base.term Prims.list) =
  fun projectee ->
    match projectee with
    | { unmatched_preconditions; remaining_context;_} -> remaining_context
type ('g, 'v) vprop_typing = unit
let (unit_const : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Base.Tm_FStar
    ((FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_Const FStar_Reflection_V2_Data.C_Unit)),
      FStar_Range.range_0)
let (proof_steps_idem : Pulse_Syntax_Base.st_term) =
  {
    Pulse_Syntax_Base.term1 =
      (Pulse_Syntax_Base.Tm_Return
         {
           Pulse_Syntax_Base.ctag = Pulse_Syntax_Base.STT_Ghost;
           Pulse_Syntax_Base.insert_eq = false;
           Pulse_Syntax_Base.term = unit_const
         });
    Pulse_Syntax_Base.range1 = FStar_Range.range_0
  }
let (proof_steps_idem_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop -> (unit, unit, unit) Pulse_Typing.st_typing)
  = fun g -> fun ctxt -> Prims.magic ()
let (post_with_emp :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t -> fun c -> fun d -> failwith "Not yet implemented:post_with_emp"
let (init_prover_state :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              unit Pulse_Checker_Auto_Util.prover_state)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun t ->
          fun c ->
            fun t_typing ->
              {
                Pulse_Checker_Auto_Util.preamble =
                  {
                    Pulse_Checker_Auto_Util.ctxt = ctxt;
                    Pulse_Checker_Auto_Util.ctxt_typing = ();
                    Pulse_Checker_Auto_Util.t = t;
                    Pulse_Checker_Auto_Util.c = c;
                    Pulse_Checker_Auto_Util.t_typing = t_typing
                  };
                Pulse_Checker_Auto_Util.matched_pre =
                  Pulse_Syntax_Base.Tm_Emp;
                Pulse_Checker_Auto_Util.unmatched_pre =
                  (Pulse_Checker_VPropEquiv.vprop_as_list
                     (Pulse_Syntax_Base.comp_pre c));
                Pulse_Checker_Auto_Util.remaining_ctxt =
                  (Pulse_Checker_VPropEquiv.vprop_as_list ctxt);
                Pulse_Checker_Auto_Util.proof_steps = proof_steps_idem;
                Pulse_Checker_Auto_Util.proof_steps_typing =
                  (post_with_emp g proof_steps_idem
                     (Pulse_Checker_Auto_Util.ghost_comp ctxt ctxt)
                     (proof_steps_idem_typing g ctxt));
                Pulse_Checker_Auto_Util.pre_equiv = ()
              }
let (step_intro_exists : Pulse_Checker_Auto_Util.prover_step_t) =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
                 (Prims.of_int (56)) (Prims.of_int (4)) (Prims.of_int (56))
                 (Prims.of_int (51)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
                 (Prims.of_int (55)) (Prims.of_int (2)) (Prims.of_int (56))
                 (Prims.of_int (51)))))
        (Obj.magic (Pulse_Checker_Auto_IntroExists.intro_exists g p))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Util.map_opt
                   (Pulse_Checker_Auto_Util.apply_intro_from_unmatched_step g
                      p) uu___)) uu___)
let (step_intro_pure : Pulse_Checker_Auto_Util.prover_step_t) =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
                 (Prims.of_int (61)) (Prims.of_int (4)) (Prims.of_int (61))
                 (Prims.of_int (47)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
                 (Prims.of_int (60)) (Prims.of_int (2)) (Prims.of_int (61))
                 (Prims.of_int (47)))))
        (Obj.magic (Pulse_Checker_Auto_IntroPure.intro_pure g p))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Util.map_opt
                   (Pulse_Checker_Auto_Util.apply_intro_from_unmatched_step g
                      p) uu___)) uu___)
let (step_intro_rewrite : Pulse_Checker_Auto_Util.prover_step_t) =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
                 (Prims.of_int (66)) (Prims.of_int (4)) (Prims.of_int (66))
                 (Prims.of_int (53)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
                 (Prims.of_int (65)) (Prims.of_int (2)) (Prims.of_int (66))
                 (Prims.of_int (53)))))
        (Obj.magic (Pulse_Checker_Auto_IntroRewrite.intro_rewrite g p))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Util.map_opt
                   (Pulse_Checker_Auto_Util.apply_intro_from_unmatched_step g
                      p) uu___)) uu___)
let rec (first_success :
  Pulse_Checker_Auto_Util.prover_step_t Prims.list ->
    Pulse_Checker_Auto_Util.prover_step_t)
  =
  fun uu___ ->
    (fun l ->
       fun g ->
         fun p ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.None)))
           | s::l1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Auto.Prover.fst"
                                (Prims.of_int (73)) (Prims.of_int (12))
                                (Prims.of_int (73)) (Prims.of_int (15)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Auto.Prover.fst"
                                (Prims.of_int (73)) (Prims.of_int (6))
                                (Prims.of_int (75)) (Prims.of_int (24)))))
                       (Obj.magic (s g p))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | FStar_Pervasives_Native.None ->
                                 Obj.magic (Obj.repr (first_success l1 g p))
                             | FStar_Pervasives_Native.Some p1 ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            FStar_Pervasives_Native.Some p1))))
                            uu___)))) uu___
let (step : Pulse_Checker_Auto_Util.prover_step_t) =
  first_success
    [Pulse_Checker_Auto_Framing.step_match;
    step_intro_exists;
    step_intro_pure;
    step_intro_rewrite]
let (finish :
  Pulse_Typing_Env.env ->
    unit Pulse_Checker_Auto_Util.prover_state ->
      (Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
        (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple3)
  =
  fun g ->
    fun p ->
      let t_typing =
        Pulse_Typing_Metatheory.st_typing_equiv_pre g
          (Pulse_Checker_Auto_Util.__proj__Mkprover_state_preamble__item__t g
             p.Pulse_Checker_Auto_Util.preamble)
          (Pulse_Checker_Auto_Util.__proj__Mkprover_state_preamble__item__c g
             p.Pulse_Checker_Auto_Util.preamble)
          (p.Pulse_Checker_Auto_Util.preamble).Pulse_Checker_Auto_Util.t_typing
          p.Pulse_Checker_Auto_Util.matched_pre () in
      let framing_token =
        FStar_Pervasives.Mkdtuple3
          ((Pulse_Checker_VPropEquiv.list_as_vprop
              p.Pulse_Checker_Auto_Util.remaining_ctxt), (), ()) in
      let uu___ =
        Pulse_Checker_Framing.apply_frame g
          (p.Pulse_Checker_Auto_Util.preamble).Pulse_Checker_Auto_Util.t
          (Pulse_Checker_Auto_Util.proof_steps_post g p) ()
          (Pulse_Typing_Metatheory.comp_st_with_pre
             (p.Pulse_Checker_Auto_Util.preamble).Pulse_Checker_Auto_Util.c
             p.Pulse_Checker_Auto_Util.matched_pre) t_typing framing_token in
      match uu___ with
      | Prims.Mkdtuple2 (uu___1, t_typing1) ->
          let uu___2 =
            Pulse_Checker_Auto_Util.bind_proof_steps_with g p
              (p.Pulse_Checker_Auto_Util.preamble).Pulse_Checker_Auto_Util.t
              uu___1 t_typing1 in
          (match uu___2 with
           | Prims.Mkdtuple2 (t, t_typing2) ->
               FStar_Pervasives.Mkdtuple3
                 (t,
                   (Pulse_Typing_Metatheory.comp_st_with_pre uu___1
                      (p.Pulse_Checker_Auto_Util.preamble).Pulse_Checker_Auto_Util.ctxt),
                   t_typing2))
let (as_failure :
  Pulse_Typing_Env.env ->
    unit Pulse_Checker_Auto_Util.prover_state -> framing_failure)
  =
  fun g ->
    fun p ->
      {
        unmatched_preconditions = (p.Pulse_Checker_Auto_Util.unmatched_pre);
        remaining_context = (p.Pulse_Checker_Auto_Util.remaining_ctxt)
      }
let rec (solve :
  Pulse_Typing_Env.env ->
    unit Pulse_Checker_Auto_Util.prover_state ->
      (((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
          (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple3,
         framing_failure) FStar_Pervasives.either,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
                 (Prims.of_int (115)) (Prims.of_int (10))
                 (Prims.of_int (115)) (Prims.of_int (16)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
                 (Prims.of_int (115)) (Prims.of_int (4)) (Prims.of_int (120))
                 (Prims.of_int (20))))) (Obj.magic (step g p))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 ->
                             FStar_Pervasives.Inr (as_failure g p))))
              | FStar_Pervasives_Native.Some p1 ->
                  Obj.magic
                    (Obj.repr
                       (match p1.Pulse_Checker_Auto_Util.unmatched_pre with
                        | [] ->
                            Obj.repr
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    FStar_Pervasives.Inl (finish g p1)))
                        | uu___1 -> Obj.repr (solve g p1)))) uu___)
let (prove_precondition :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              (((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
                  (unit, unit, unit) Pulse_Typing.st_typing)
                  FStar_Pervasives.dtuple3,
                 framing_failure) FStar_Pervasives.either,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun t ->
          fun c ->
            fun t_typing ->
              solve g (init_prover_state g ctxt () t c t_typing)