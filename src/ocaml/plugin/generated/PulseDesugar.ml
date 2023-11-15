open Prims
type error =
  (Prims.string * FStar_Compiler_Range_Type.range)
    FStar_Pervasives_Native.option
type 'a err = Prims.nat -> (('a, error) FStar_Pervasives.either * Prims.nat)
let op_let_Question :
  'a 'b .
    'a err ->
      ('a -> 'b err) ->
        Prims.nat -> (('b, error) FStar_Pervasives.either * Prims.nat)
  =
  fun f ->
    fun g ->
      fun ctr ->
        let uu___ = f ctr in
        match uu___ with
        | (FStar_Pervasives.Inl a1, ctr1) -> let uu___1 = g a1 in uu___1 ctr1
        | (FStar_Pervasives.Inr e, ctr1) -> ((FStar_Pervasives.Inr e), ctr1)
let return : 'a . 'a -> 'a err =
  fun x -> fun ctr -> ((FStar_Pervasives.Inl x), ctr)
let fail : 'a . Prims.string -> FStar_Compiler_Range_Type.range -> 'a err =
  fun message ->
    fun range ->
      fun ctr ->
        ((FStar_Pervasives.Inr
            (FStar_Pervasives_Native.Some (message, range))), ctr)
let just_fail : 'a . unit -> 'a err =
  fun uu___ ->
    fun ctr -> ((FStar_Pervasives.Inr FStar_Pervasives_Native.None), ctr)
let (next_ctr : Prims.nat err) =
  fun ctr ->
    ((FStar_Pervasives.Inl (ctr + Prims.int_one)), (ctr + Prims.int_one))
let rec map_err :
  'a 'b . ('a -> 'b err) -> 'a Prims.list -> 'b Prims.list err =
  fun f ->
    fun l ->
      match l with
      | [] -> return []
      | hd::tl ->
          let uu___ = f hd in
          op_let_Question uu___
            (fun hd1 ->
               let uu___1 = map_err f tl in
               op_let_Question uu___1 (fun tl1 -> return (hd1 :: tl1)))
let rec fold_err :
  'a 'b . ('b -> 'a -> 'b err) -> 'a Prims.list -> 'b -> 'b err =
  fun f ->
    fun l ->
      fun x ->
        match l with
        | [] -> return x
        | hd::tl ->
            let uu___ = f x hd in
            op_let_Question uu___ (fun x1 -> fold_err f tl x1)
let map_err_opt :
  'a 'b .
    ('a -> 'b err) ->
      'a FStar_Pervasives_Native.option ->
        'b FStar_Pervasives_Native.option err
  =
  fun f ->
    fun o ->
      match o with
      | FStar_Pervasives_Native.None -> return FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some v ->
          let uu___ = f v in
          op_let_Question uu___
            (fun v' -> return (FStar_Pervasives_Native.Some v'))
let (as_term : FStar_Syntax_Syntax.term -> PulseSyntaxWrapper.term) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_unknown ->
        PulseSyntaxWrapper.tm_unknown t.FStar_Syntax_Syntax.pos
    | uu___ -> PulseSyntaxWrapper.tm_expr t t.FStar_Syntax_Syntax.pos
type env_t =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  local_refs: FStar_Ident.ident Prims.list }
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee -> match projectee with | { tcenv; local_refs;_} -> tcenv
let (__proj__Mkenv_t__item__local_refs :
  env_t -> FStar_Ident.ident Prims.list) =
  fun projectee ->
    match projectee with | { tcenv; local_refs;_} -> local_refs
let (push_bv :
  env_t -> FStar_Ident.ident -> (env_t * FStar_Syntax_Syntax.bv)) =
  fun env ->
    fun x ->
      let uu___ =
        FStar_Syntax_DsEnv.push_bv (env.tcenv).FStar_TypeChecker_Env.dsenv x in
      match uu___ with
      | (dsenv, bv) ->
          let tcenv =
            let uu___1 = env.tcenv in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___1.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___1.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = (uu___1.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.intactics =
                (uu___1.FStar_TypeChecker_Env.intactics);
              FStar_TypeChecker_Env.nocoerce =
                (uu___1.FStar_TypeChecker_Env.nocoerce);
              FStar_TypeChecker_Env.tc_term =
                (uu___1.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                (uu___1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
              FStar_TypeChecker_Env.universe_of =
                (uu___1.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                (uu___1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
              FStar_TypeChecker_Env.teq_nosmt_force =
                (uu___1.FStar_TypeChecker_Env.teq_nosmt_force);
              FStar_TypeChecker_Env.subtype_nosmt_force =
                (uu___1.FStar_TypeChecker_Env.subtype_nosmt_force);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv = dsenv;
              FStar_TypeChecker_Env.nbe = (uu___1.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___1.FStar_TypeChecker_Env.enable_defer_to_tac);
              FStar_TypeChecker_Env.unif_allow_ref_guards =
                (uu___1.FStar_TypeChecker_Env.unif_allow_ref_guards);
              FStar_TypeChecker_Env.erase_erasable_args =
                (uu___1.FStar_TypeChecker_Env.erase_erasable_args);
              FStar_TypeChecker_Env.core_check =
                (uu___1.FStar_TypeChecker_Env.core_check)
            } in
          let env1 = { tcenv; local_refs = (env.local_refs) } in (env1, bv)
let rec (push_bvs :
  env_t ->
    FStar_Ident.ident Prims.list ->
      (env_t * FStar_Syntax_Syntax.bv Prims.list))
  =
  fun env ->
    fun xs ->
      match xs with
      | [] -> (env, [])
      | x::xs1 ->
          let uu___ = push_bv env x in
          (match uu___ with
           | (env1, bv) ->
               let uu___1 = push_bvs env1 xs1 in
               (match uu___1 with | (env2, bvs) -> (env2, (bv :: bvs))))
let (push_namespace : env_t -> FStar_Ident.lident -> env_t) =
  fun env ->
    fun lid ->
      let dsenv =
        FStar_Syntax_DsEnv.push_namespace
          (env.tcenv).FStar_TypeChecker_Env.dsenv lid in
      let tcenv =
        let uu___ = env.tcenv in
        {
          FStar_TypeChecker_Env.solver = (uu___.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range = (uu___.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma = (uu___.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab = (uu___.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq_strict =
            (uu___.FStar_TypeChecker_Env.use_eq_strict);
          FStar_TypeChecker_Env.is_iface =
            (uu___.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit = (uu___.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax = (uu___.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 = (uu___.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard =
            (uu___.FStar_TypeChecker_Env.failhard);
          FStar_TypeChecker_Env.nosynth =
            (uu___.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.intactics =
            (uu___.FStar_TypeChecker_Env.intactics);
          FStar_TypeChecker_Env.nocoerce =
            (uu___.FStar_TypeChecker_Env.nocoerce);
          FStar_TypeChecker_Env.tc_term =
            (uu___.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
            (uu___.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
          FStar_TypeChecker_Env.universe_of =
            (uu___.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
            (uu___.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
          FStar_TypeChecker_Env.teq_nosmt_force =
            (uu___.FStar_TypeChecker_Env.teq_nosmt_force);
          FStar_TypeChecker_Env.subtype_nosmt_force =
            (uu___.FStar_TypeChecker_Env.subtype_nosmt_force);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.fv_delta_depths =
            (uu___.FStar_TypeChecker_Env.fv_delta_depths);
          FStar_TypeChecker_Env.proof_ns =
            (uu___.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.try_solve_implicits_hook =
            (uu___.FStar_TypeChecker_Env.try_solve_implicits_hook);
          FStar_TypeChecker_Env.splice = (uu___.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.mpreprocess =
            (uu___.FStar_TypeChecker_Env.mpreprocess);
          FStar_TypeChecker_Env.postprocess =
            (uu___.FStar_TypeChecker_Env.postprocess);
          FStar_TypeChecker_Env.identifier_info =
            (uu___.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv = dsenv;
          FStar_TypeChecker_Env.nbe = (uu___.FStar_TypeChecker_Env.nbe);
          FStar_TypeChecker_Env.strict_args_tab =
            (uu___.FStar_TypeChecker_Env.strict_args_tab);
          FStar_TypeChecker_Env.erasable_types_tab =
            (uu___.FStar_TypeChecker_Env.erasable_types_tab);
          FStar_TypeChecker_Env.enable_defer_to_tac =
            (uu___.FStar_TypeChecker_Env.enable_defer_to_tac);
          FStar_TypeChecker_Env.unif_allow_ref_guards =
            (uu___.FStar_TypeChecker_Env.unif_allow_ref_guards);
          FStar_TypeChecker_Env.erase_erasable_args =
            (uu___.FStar_TypeChecker_Env.erase_erasable_args);
          FStar_TypeChecker_Env.core_check =
            (uu___.FStar_TypeChecker_Env.core_check)
        } in
      let env1 = { tcenv; local_refs = (env.local_refs) } in env1
let (desugar_const : FStar_Const.sconst -> PulseSyntaxWrapper.constant) =
  fun c -> PulseSyntaxWrapper.inspect_const c
let (r_ : FStar_Compiler_Range_Type.range) =
  FStar_Compiler_Range_Type.dummyRange
let (admit_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Prims"; "admit"] r_
let (pulse_lib_core_lid : Prims.string -> FStar_Ident.lident) =
  fun l ->
    FStar_Ident.lid_of_path
      (FStar_List_Tot_Base.op_At ["Pulse"; "Lib"; "Core"] [l]) r_
let (pulse_lib_ref_lid : Prims.string -> FStar_Ident.lident) =
  fun l ->
    FStar_Ident.lid_of_path
      (FStar_List_Tot_Base.op_At ["Pulse"; "Lib"; "Reference"] [l]) r_
let (star_lid : FStar_Ident.lident) = pulse_lib_core_lid "op_Star_Star"
let (emp_lid : FStar_Ident.lident) = pulse_lib_core_lid "emp"
let (pure_lid : FStar_Ident.lident) = pulse_lib_core_lid "pure"
let (stt_lid : FStar_Ident.lident) = pulse_lib_core_lid "stt"
let (assign_lid : FStar_Ident.lident) = pulse_lib_ref_lid "op_Colon_Equals"
let (stt_ghost_lid : FStar_Ident.lident) = pulse_lib_core_lid "stt_ghost"
let (stt_atomic_lid : FStar_Ident.lident) = pulse_lib_core_lid "stt_atomic"
let (op_colon_equals_lid :
  FStar_Compiler_Range_Type.range -> FStar_Ident.lident) =
  fun r -> FStar_Ident.lid_of_path ["op_Colon_Equals"] r
let (op_array_assignment_lid :
  FStar_Compiler_Range_Type.range -> FStar_Ident.lident) =
  fun r -> FStar_Ident.lid_of_path ["op_Array_Assignment"] r
let (op_bang_lid : FStar_Ident.lident) = pulse_lib_ref_lid "op_Bang"
let (read : FStar_Ident.ident -> FStar_Parser_AST.term) =
  fun x ->
    let range = FStar_Ident.range_of_id x in
    let level = FStar_Parser_AST.Un in
    let head =
      {
        FStar_Parser_AST.tm = (FStar_Parser_AST.Var op_bang_lid);
        FStar_Parser_AST.range = range;
        FStar_Parser_AST.level = level
      } in
    let arg =
      let uu___ =
        let uu___1 = FStar_Ident.lid_of_ids [x] in
        FStar_Parser_AST.Var uu___1 in
      {
        FStar_Parser_AST.tm = uu___;
        FStar_Parser_AST.range = range;
        FStar_Parser_AST.level = level
      } in
    {
      FStar_Parser_AST.tm =
        (FStar_Parser_AST.App (head, arg, FStar_Parser_AST.Nothing));
      FStar_Parser_AST.range = range;
      FStar_Parser_AST.level = level
    }
let (stapp_assignment :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term Prims.list ->
      FStar_Syntax_Syntax.term ->
        PulseSyntaxWrapper.range -> PulseSyntaxWrapper.st_term)
  =
  fun assign_lid1 ->
    fun args ->
      fun last_arg ->
        fun r ->
          let head_fv =
            FStar_Syntax_Syntax.lid_as_fv assign_lid1
              FStar_Pervasives_Native.None in
          let head = FStar_Syntax_Syntax.fv_to_tm head_fv in
          let app =
            FStar_Compiler_List.fold_left
              (fun head1 ->
                 fun arg ->
                   FStar_Syntax_Syntax.mk_Tm_app head1
                     [(arg, FStar_Pervasives_Native.None)]
                     arg.FStar_Syntax_Syntax.pos) head args in
          let uu___ = PulseSyntaxWrapper.tm_expr app r in
          let uu___1 = as_term last_arg in
          PulseSyntaxWrapper.tm_st_app uu___ FStar_Pervasives_Native.None
            uu___1 r
let (resolve_lid : env_t -> FStar_Ident.lident -> FStar_Ident.lident err) =
  fun env ->
    fun lid ->
      let uu___ =
        FStar_Syntax_DsEnv.try_lookup_lid
          (env.tcenv).FStar_TypeChecker_Env.dsenv lid in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 = FStar_Ident.string_of_lid lid in
            FStar_Compiler_Util.format1 "Name %s not found" uu___2 in
          let uu___2 = FStar_Ident.range_of_lid lid in fail uu___1 uu___2
      | FStar_Pervasives_Native.Some t ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Subst.compress t in
            uu___2.FStar_Syntax_Syntax.n in
          (match uu___1 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu___2 = FStar_Syntax_Syntax.lid_of_fv fv in return uu___2
           | uu___2 ->
               let uu___3 =
                 let uu___4 = FStar_Ident.string_of_lid lid in
                 let uu___5 = FStar_Syntax_Print.term_to_string t in
                 FStar_Compiler_Util.format2
                   "Name %s resolved unexpectedly to %s" uu___4 uu___5 in
               let uu___4 = FStar_Ident.range_of_lid lid in
               fail uu___3 uu___4)
let (ret : FStar_Syntax_Syntax.term -> PulseSyntaxWrapper.st_term) =
  fun s ->
    let uu___ = as_term s in
    PulseSyntaxWrapper.tm_return uu___ s.FStar_Syntax_Syntax.pos
type admit_or_return_t =
  | STTerm of PulseSyntaxWrapper.st_term 
  | Return of FStar_Syntax_Syntax.term 
let (uu___is_STTerm : admit_or_return_t -> Prims.bool) =
  fun projectee -> match projectee with | STTerm _0 -> true | uu___ -> false
let (__proj__STTerm__item___0 :
  admit_or_return_t -> PulseSyntaxWrapper.st_term) =
  fun projectee -> match projectee with | STTerm _0 -> _0
let (uu___is_Return : admit_or_return_t -> Prims.bool) =
  fun projectee -> match projectee with | Return _0 -> true | uu___ -> false
let (__proj__Return__item___0 :
  admit_or_return_t -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Return _0 -> _0
let (st_term_of_admit_or_return :
  admit_or_return_t -> PulseSyntaxWrapper.st_term) =
  fun t -> match t with | STTerm t1 -> t1 | Return t1 -> ret t1
let (admit_or_return :
  env_t -> FStar_Syntax_Syntax.term -> admit_or_return_t) =
  fun env ->
    fun s ->
      let r = s.FStar_Syntax_Syntax.pos in
      let uu___ = FStar_Syntax_Util.head_and_args_full s in
      match uu___ with
      | (head, args) ->
          (match head.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu___1 = FStar_Syntax_Syntax.fv_eq_lid fv admit_lid in
               if uu___1
               then
                 let uu___2 = PulseSyntaxWrapper.tm_admit r in STTerm uu___2
               else Return s
           | uu___1 -> Return s)
let (prepend_ctx_issue :
  FStar_Pprint.document -> FStar_Errors.issue -> FStar_Errors.issue) =
  fun c ->
    fun i ->
      {
        FStar_Errors.issue_msg = (c :: (i.FStar_Errors.issue_msg));
        FStar_Errors.issue_level = (i.FStar_Errors.issue_level);
        FStar_Errors.issue_range = (i.FStar_Errors.issue_range);
        FStar_Errors.issue_number = (i.FStar_Errors.issue_number);
        FStar_Errors.issue_ctx = (i.FStar_Errors.issue_ctx)
      }
let (tosyntax' :
  env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term err) =
  fun env ->
    fun t ->
      try
        (fun uu___ ->
           match () with
           | () ->
               let uu___1 =
                 FStar_ToSyntax_ToSyntax.desugar_term
                   (env.tcenv).FStar_TypeChecker_Env.dsenv t in
               return uu___1) ()
      with
      | uu___ ->
          let uu___1 = FStar_Errors.issue_of_exn uu___ in
          (match uu___1 with
           | FStar_Pervasives_Native.Some i ->
               let i1 =
                 let uu___2 =
                   FStar_Pprint.arbitrary_string
                     "Failed to desugar Pulse term" in
                 prepend_ctx_issue uu___2 i in
               (FStar_Errors.add_issues [i1]; just_fail ())
           | FStar_Pervasives_Native.None ->
               let uu___2 =
                 let uu___3 = FStar_Parser_AST.term_to_string t in
                 let uu___4 = PulseSyntaxWrapper.print_exn uu___ in
                 FStar_Compiler_Util.format2
                   "Failed to desugar Pulse term %s\nUnexpected exception: %s\n"
                   uu___3 uu___4 in
               fail uu___2 t.FStar_Parser_AST.range)
let (tosyntax :
  env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term err) =
  fun env ->
    fun t ->
      let uu___ = tosyntax' env t in
      op_let_Question uu___ (fun s -> return s)
let (desugar_term :
  env_t -> FStar_Parser_AST.term -> PulseSyntaxWrapper.term err) =
  fun env ->
    fun t ->
      let uu___ = tosyntax env t in
      op_let_Question uu___
        (fun s -> let uu___1 = as_term s in return uu___1)
let (desugar_term_opt :
  env_t ->
    FStar_Parser_AST.term FStar_Pervasives_Native.option ->
      PulseSyntaxWrapper.term err)
  =
  fun env ->
    fun t ->
      match t with
      | FStar_Pervasives_Native.None ->
          let uu___ =
            PulseSyntaxWrapper.tm_unknown
              FStar_Compiler_Range_Type.dummyRange in
          return uu___
      | FStar_Pervasives_Native.Some e -> desugar_term env e
let (interpret_vprop_constructors :
  env_t -> FStar_Syntax_Syntax.term -> PulseSyntaxWrapper.term) =
  fun env ->
    fun v ->
      let uu___ = FStar_Syntax_Util.head_and_args_full v in
      match uu___ with
      | (head, args) ->
          (match ((head.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___1)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv pure_lid ->
               let res =
                 let uu___2 = as_term l in
                 PulseSyntaxWrapper.tm_pure uu___2 v.FStar_Syntax_Syntax.pos in
               res
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv emp_lid ->
               PulseSyntaxWrapper.tm_emp v.FStar_Syntax_Syntax.pos
           | uu___1 -> as_term v)
let rec (desugar_vprop :
  env_t -> PulseSugar.vprop -> PulseSyntaxWrapper.vprop err) =
  fun env ->
    fun v ->
      match v.PulseSugar.v with
      | PulseSugar.VPropTerm t ->
          let uu___ = tosyntax env t in
          op_let_Question uu___
            (fun t1 ->
               let uu___1 = interpret_vprop_constructors env t1 in
               return uu___1)
      | PulseSugar.VPropStar (v1, v2) ->
          let uu___ = desugar_vprop env v1 in
          op_let_Question uu___
            (fun v11 ->
               let uu___1 = desugar_vprop env v2 in
               op_let_Question uu___1
                 (fun v21 ->
                    let uu___2 =
                      PulseSyntaxWrapper.tm_star v11 v21 v.PulseSugar.vrange in
                    return uu___2))
      | PulseSugar.VPropExists
          { PulseSugar.binders = binders; PulseSugar.body = body;_} ->
          let rec aux env1 binders1 =
            match binders1 with
            | [] -> desugar_vprop env1 body
            | (uu___, i, t)::bs ->
                let uu___1 = desugar_term env1 t in
                op_let_Question uu___1
                  (fun t1 ->
                     let uu___2 = push_bv env1 i in
                     match uu___2 with
                     | (env2, bv) ->
                         let uu___3 = aux env2 bs in
                         op_let_Question uu___3
                           (fun body1 ->
                              let body2 =
                                PulseSyntaxWrapper.close_term body1
                                  bv.FStar_Syntax_Syntax.index in
                              let b = PulseSyntaxWrapper.mk_binder i t1 in
                              let uu___4 =
                                PulseSyntaxWrapper.tm_exists b body2
                                  v.PulseSugar.vrange in
                              return uu___4)) in
          aux env binders
let (mk_totbind :
  PulseSyntaxWrapper.binder ->
    PulseSyntaxWrapper.term ->
      PulseSyntaxWrapper.st_term ->
        PulseSyntaxWrapper.range -> PulseSyntaxWrapper.st_term)
  =
  fun b ->
    fun s1 -> fun s2 -> fun r -> PulseSyntaxWrapper.tm_totbind b s1 s2 r
let (mk_bind :
  PulseSyntaxWrapper.binder ->
    PulseSyntaxWrapper.st_term ->
      PulseSyntaxWrapper.st_term ->
        PulseSyntaxWrapper.range -> PulseSyntaxWrapper.st_term)
  =
  fun b -> fun s1 -> fun s2 -> fun r -> PulseSyntaxWrapper.tm_bind b s1 s2 r
let (explicit_rvalues : env_t -> PulseSugar.stmt -> PulseSugar.stmt) =
  fun env -> fun s -> s
type qual = PulseSyntaxWrapper.qualifier FStar_Pervasives_Native.option
let (as_qual : FStar_Parser_AST.aqual -> qual) =
  fun q ->
    match q with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) ->
        PulseSyntaxWrapper.as_qual true
    | uu___ -> PulseSyntaxWrapper.as_qual false
let (resolve_names :
  env_t ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option err)
  =
  fun env ->
    fun ns ->
      match ns with
      | FStar_Pervasives_Native.None -> return FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ns1 ->
          let uu___ = map_err (resolve_lid env) ns1 in
          op_let_Question uu___
            (fun ns2 -> return (FStar_Pervasives_Native.Some ns2))
let (desugar_hint_type :
  env_t -> PulseSugar.hint_type -> PulseSyntaxWrapper.hint_type err) =
  fun env ->
    fun ht ->
      match ht with
      | PulseSugar.ASSERT vp ->
          let uu___ = desugar_vprop env vp in
          op_let_Question uu___
            (fun vp1 ->
               let uu___1 = PulseSyntaxWrapper.mk_assert_hint_type vp1 in
               return uu___1)
      | PulseSugar.UNFOLD (ns, vp) ->
          let uu___ = desugar_vprop env vp in
          op_let_Question uu___
            (fun vp1 ->
               let uu___1 = resolve_names env ns in
               op_let_Question uu___1
                 (fun ns1 ->
                    let ns2 =
                      FStar_Compiler_Util.map_opt ns1
                        (FStar_Compiler_List.map FStar_Ident.string_of_lid) in
                    let uu___2 =
                      PulseSyntaxWrapper.mk_unfold_hint_type ns2 vp1 in
                    return uu___2))
      | PulseSugar.FOLD (ns, vp) ->
          let uu___ = desugar_vprop env vp in
          op_let_Question uu___
            (fun vp1 ->
               let uu___1 = resolve_names env ns in
               op_let_Question uu___1
                 (fun ns1 ->
                    let ns2 =
                      FStar_Compiler_Util.map_opt ns1
                        (FStar_Compiler_List.map FStar_Ident.string_of_lid) in
                    let uu___2 = PulseSyntaxWrapper.mk_fold_hint_type ns2 vp1 in
                    return uu___2))
      | PulseSugar.RENAME (pairs, goal) ->
          let uu___ =
            map_err
              (fun uu___1 ->
                 match uu___1 with
                 | (t1, t2) ->
                     let uu___2 = desugar_term env t1 in
                     op_let_Question uu___2
                       (fun t11 ->
                          let uu___3 = desugar_term env t2 in
                          op_let_Question uu___3
                            (fun t21 -> return (t11, t21)))) pairs in
          op_let_Question uu___
            (fun pairs1 ->
               let uu___1 = map_err_opt (desugar_vprop env) goal in
               op_let_Question uu___1
                 (fun goal1 ->
                    let uu___2 =
                      PulseSyntaxWrapper.mk_rename_hint_type pairs1 goal1 in
                    return uu___2))
      | PulseSugar.REWRITE (t1, t2) ->
          let uu___ = desugar_vprop env t1 in
          op_let_Question uu___
            (fun t11 ->
               let uu___1 = desugar_vprop env t2 in
               op_let_Question uu___1
                 (fun t21 ->
                    let uu___2 =
                      PulseSyntaxWrapper.mk_rewrite_hint_type t11 t21 in
                    return uu___2))
let (desugar_datacon : env_t -> FStar_Ident.lid -> PulseSyntaxWrapper.fv err)
  =
  fun env ->
    fun l ->
      let rng = FStar_Ident.range_of_lid l in
      let t =
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Name l) rng
          FStar_Parser_AST.Expr in
      let uu___ = tosyntax env t in
      op_let_Question uu___
        (fun tt ->
           let uu___1 =
             let uu___2 =
               let uu___3 = FStar_Syntax_Subst.compress tt in
               uu___3.FStar_Syntax_Syntax.n in
             match uu___2 with
             | FStar_Syntax_Syntax.Tm_fvar fv -> return fv
             | FStar_Syntax_Syntax.Tm_uinst
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu___3;
                    FStar_Syntax_Syntax.vars = uu___4;
                    FStar_Syntax_Syntax.hash_code = uu___5;_},
                  uu___6)
                 -> return fv
             | uu___3 ->
                 let uu___4 =
                   let uu___5 = FStar_Ident.string_of_lid l in
                   FStar_Compiler_Util.format1 "Not a datacon? %s" uu___5 in
                 fail uu___4 rng in
           op_let_Question uu___1
             (fun sfv ->
                let uu___2 =
                  let uu___3 = FStar_Syntax_Syntax.lid_of_fv sfv in
                  PulseSyntaxWrapper.mk_fv uu___3 rng in
                return uu___2))
let rec (desugar_stmt :
  env_t -> PulseSugar.stmt -> PulseSyntaxWrapper.st_term err) =
  fun env ->
    fun s ->
      match s.PulseSugar.s with
      | PulseSugar.Expr { PulseSugar.e = e;_} ->
          let uu___ = tosyntax env e in
          op_let_Question uu___
            (fun tm ->
               let uu___1 =
                 let uu___2 = admit_or_return env tm in
                 st_term_of_admit_or_return uu___2 in
               return uu___1)
      | PulseSugar.Assignment
          { PulseSugar.lhs = lhs; PulseSugar.value = value;_} ->
          let uu___ = tosyntax env lhs in
          op_let_Question uu___
            (fun lhs1 ->
               let uu___1 = tosyntax env value in
               op_let_Question uu___1
                 (fun rhs ->
                    let uu___2 =
                      let uu___3 = op_colon_equals_lid s.PulseSugar.range1 in
                      resolve_lid env uu___3 in
                    op_let_Question uu___2
                      (fun assignment_lid ->
                         let uu___3 =
                           stapp_assignment assignment_lid [lhs1] rhs
                             s.PulseSugar.range1 in
                         return uu___3)))
      | PulseSugar.ArrayAssignment
          { PulseSugar.arr = arr; PulseSugar.index = index;
            PulseSugar.value1 = value;_}
          ->
          let uu___ = tosyntax env arr in
          op_let_Question uu___
            (fun arr1 ->
               let uu___1 = tosyntax env index in
               op_let_Question uu___1
                 (fun index1 ->
                    let uu___2 = tosyntax env value in
                    op_let_Question uu___2
                      (fun value1 ->
                         let uu___3 =
                           let uu___4 =
                             op_array_assignment_lid s.PulseSugar.range1 in
                           resolve_lid env uu___4 in
                         op_let_Question uu___3
                           (fun array_assignment_lid ->
                              let uu___4 =
                                stapp_assignment array_assignment_lid
                                  [arr1; index1] value1 s.PulseSugar.range1 in
                              return uu___4))))
      | PulseSugar.Sequence
          {
            PulseSugar.s1 =
              { PulseSugar.s = PulseSugar.Open l;
                PulseSugar.range1 = uu___;_};
            PulseSugar.s2 = s2;_}
          -> let env1 = push_namespace env l in desugar_stmt env1 s2
      | PulseSugar.Sequence
          {
            PulseSugar.s1 =
              { PulseSugar.s = PulseSugar.LetBinding lb;
                PulseSugar.range1 = uu___;_};
            PulseSugar.s2 = s2;_}
          -> desugar_bind env lb s2 s.PulseSugar.range1
      | PulseSugar.ProofHintWithBinders uu___ ->
          desugar_proof_hint_with_binders env s FStar_Pervasives_Native.None
            s.PulseSugar.range1
      | PulseSugar.Sequence { PulseSugar.s1 = s1; PulseSugar.s2 = s2;_} when
          PulseSugar.uu___is_ProofHintWithBinders s1.PulseSugar.s ->
          desugar_proof_hint_with_binders env s1
            (FStar_Pervasives_Native.Some s2) s.PulseSugar.range1
      | PulseSugar.Sequence { PulseSugar.s1 = s1; PulseSugar.s2 = s2;_} ->
          desugar_sequence env s1 s2 s.PulseSugar.range1
      | PulseSugar.Block { PulseSugar.stmt = stmt;_} -> desugar_stmt env stmt
      | PulseSugar.If
          { PulseSugar.head1 = head; PulseSugar.join_vprop = join_vprop;
            PulseSugar.then_ = then_; PulseSugar.else_opt = else_opt;_}
          ->
          let uu___ = desugar_term env head in
          op_let_Question uu___
            (fun head1 ->
               let uu___1 =
                 match join_vprop with
                 | FStar_Pervasives_Native.None ->
                     return FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some t ->
                     let uu___2 = desugar_vprop env t in
                     op_let_Question uu___2
                       (fun vp -> return (FStar_Pervasives_Native.Some vp)) in
               op_let_Question uu___1
                 (fun join_vprop1 ->
                    let uu___2 = desugar_stmt env then_ in
                    op_let_Question uu___2
                      (fun then_1 ->
                         let uu___3 =
                           match else_opt with
                           | FStar_Pervasives_Native.None ->
                               let uu___4 =
                                 let uu___5 =
                                   PulseSyntaxWrapper.tm_expr
                                     FStar_Syntax_Syntax.unit_const
                                     FStar_Compiler_Range_Type.dummyRange in
                                 PulseSyntaxWrapper.tm_return uu___5
                                   FStar_Compiler_Range_Type.dummyRange in
                               return uu___4
                           | FStar_Pervasives_Native.Some e ->
                               desugar_stmt env e in
                         op_let_Question uu___3
                           (fun else_ ->
                              let uu___4 =
                                PulseSyntaxWrapper.tm_if head1 join_vprop1
                                  then_1 else_ s.PulseSugar.range1 in
                              return uu___4))))
      | PulseSugar.Match
          { PulseSugar.head2 = head;
            PulseSugar.returns_annot = returns_annot;
            PulseSugar.branches = branches;_}
          ->
          let uu___ = desugar_term env head in
          op_let_Question uu___
            (fun head1 ->
               let uu___1 = map_err_opt (desugar_vprop env) returns_annot in
               op_let_Question uu___1
                 (fun returns_annot1 ->
                    let uu___2 = map_err (desugar_branch env) branches in
                    op_let_Question uu___2
                      (fun branches1 ->
                         let uu___3 =
                           PulseSyntaxWrapper.tm_match head1 returns_annot1
                             branches1 s.PulseSugar.range1 in
                         return uu___3)))
      | PulseSugar.While
          { PulseSugar.guard = guard; PulseSugar.id1 = id;
            PulseSugar.invariant = invariant; PulseSugar.body1 = body;_}
          ->
          let uu___ = desugar_stmt env guard in
          op_let_Question uu___
            (fun guard1 ->
               let uu___1 =
                 let uu___2 = push_bv env id in
                 match uu___2 with
                 | (env1, bv) ->
                     let uu___3 = desugar_vprop env1 invariant in
                     op_let_Question uu___3
                       (fun inv ->
                          let uu___4 =
                            PulseSyntaxWrapper.close_term inv
                              bv.FStar_Syntax_Syntax.index in
                          return uu___4) in
               op_let_Question uu___1
                 (fun invariant1 ->
                    let uu___2 = desugar_stmt env body in
                    op_let_Question uu___2
                      (fun body1 ->
                         let uu___3 =
                           PulseSyntaxWrapper.tm_while guard1
                             (id, invariant1) body1 s.PulseSugar.range1 in
                         return uu___3)))
      | PulseSugar.Introduce
          { PulseSugar.vprop = vprop; PulseSugar.witnesses = witnesses;_} ->
          (match vprop.PulseSugar.v with
           | PulseSugar.VPropTerm uu___ ->
               fail "introduce expects an existential formula"
                 s.PulseSugar.range1
           | PulseSugar.VPropExists uu___ ->
               let uu___1 = desugar_vprop env vprop in
               op_let_Question uu___1
                 (fun vp ->
                    let uu___2 = map_err (desugar_term env) witnesses in
                    op_let_Question uu___2
                      (fun witnesses1 ->
                         let uu___3 =
                           PulseSyntaxWrapper.tm_intro_exists vp witnesses1
                             s.PulseSugar.range1 in
                         return uu___3)))
      | PulseSugar.Parallel
          { PulseSugar.p1 = p1; PulseSugar.p2 = p2; PulseSugar.q1 = q1;
            PulseSugar.q2 = q2; PulseSugar.b1 = b1; PulseSugar.b2 = b2;_}
          ->
          let uu___ = desugar_vprop env p1 in
          op_let_Question uu___
            (fun p11 ->
               let uu___1 = desugar_vprop env p2 in
               op_let_Question uu___1
                 (fun p21 ->
                    let uu___2 = desugar_vprop env q1 in
                    op_let_Question uu___2
                      (fun q11 ->
                         let uu___3 = desugar_vprop env q2 in
                         op_let_Question uu___3
                           (fun q21 ->
                              let uu___4 = desugar_stmt env b1 in
                              op_let_Question uu___4
                                (fun b11 ->
                                   let uu___5 = desugar_stmt env b2 in
                                   op_let_Question uu___5
                                     (fun b21 ->
                                        let uu___6 =
                                          PulseSyntaxWrapper.tm_par p11 p21
                                            q11 q21 b11 b21
                                            s.PulseSugar.range1 in
                                        return uu___6))))))
      | PulseSugar.Rewrite { PulseSugar.p11 = p1; PulseSugar.p21 = p2;_} ->
          let uu___ = desugar_vprop env p1 in
          op_let_Question uu___
            (fun p11 ->
               let uu___1 = desugar_vprop env p2 in
               op_let_Question uu___1
                 (fun p21 ->
                    let uu___2 =
                      PulseSyntaxWrapper.tm_rewrite p11 p21
                        s.PulseSugar.range1 in
                    return uu___2))
      | PulseSugar.LetBinding uu___ ->
          fail "Terminal let binding" s.PulseSugar.range1
      | PulseSugar.WithInvariants
          { PulseSugar.names = n1::names; PulseSugar.body2 = body;
            PulseSugar.returns_ = returns_;_}
          ->
          let uu___ = tosyntax env n1 in
          op_let_Question uu___
            (fun n11 ->
               let uu___1 = map_err (tosyntax env) names in
               op_let_Question uu___1
                 (fun names1 ->
                    let uu___2 = desugar_stmt env body in
                    op_let_Question uu___2
                      (fun body1 ->
                         let uu___3 =
                           map_err_opt (desugar_vprop env) returns_ in
                         op_let_Question uu___3
                           (fun returns_1 ->
                              let tt =
                                FStar_Compiler_List.fold_right
                                  (fun nm ->
                                     fun body2 ->
                                       let nm1 =
                                         PulseSyntaxWrapper.tm_expr nm
                                           s.PulseSugar.range1 in
                                       PulseSyntaxWrapper.tm_with_inv nm1
                                         body2 FStar_Pervasives_Native.None
                                         s.PulseSugar.range1) names1 body1 in
                              let n12 =
                                PulseSyntaxWrapper.tm_expr n11
                                  s.PulseSugar.range1 in
                              let uu___4 =
                                PulseSyntaxWrapper.tm_with_inv n12 tt
                                  returns_1 s.PulseSugar.range1 in
                              return uu___4))))
and (desugar_branch :
  env_t ->
    (FStar_Parser_AST.pattern * PulseSugar.stmt) ->
      PulseSyntaxWrapper.branch err)
  =
  fun env ->
    fun br ->
      let uu___ = br in
      match uu___ with
      | (p, e) ->
          let uu___1 = desugar_pat env p in
          op_let_Question uu___1
            (fun uu___2 ->
               match uu___2 with
               | (p1, vs) ->
                   let uu___3 = push_bvs env vs in
                   (match uu___3 with
                    | (env1, bvs) ->
                        let uu___4 = desugar_stmt env1 e in
                        op_let_Question uu___4
                          (fun e1 ->
                             let e2 =
                               let uu___5 =
                                 FStar_Compiler_List.map
                                   (fun v -> v.FStar_Syntax_Syntax.index) bvs in
                               PulseSyntaxWrapper.close_st_term_n e1 uu___5 in
                             return (p1, e2))))
and (desugar_pat :
  env_t ->
    FStar_Parser_AST.pattern ->
      (PulseSyntaxWrapper.pattern * FStar_Ident.ident Prims.list) err)
  =
  fun env ->
    fun p ->
      let r = p.FStar_Parser_AST.prange in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatVar (id, uu___, uu___1) ->
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Ident.string_of_id id in
              PulseSyntaxWrapper.pat_var uu___4 r in
            (uu___3, [id]) in
          return uu___2
      | FStar_Parser_AST.PatWild uu___ ->
          let id = FStar_Ident.mk_ident ("_", r) in
          let uu___1 =
            let uu___2 = PulseSyntaxWrapper.pat_var "_" r in (uu___2, [id]) in
          return uu___1
      | FStar_Parser_AST.PatConst c ->
          let c1 = desugar_const c in
          let uu___ =
            let uu___1 = PulseSyntaxWrapper.pat_constant c1 r in (uu___1, []) in
          return uu___
      | FStar_Parser_AST.PatName lid ->
          let uu___ = desugar_datacon env lid in
          op_let_Question uu___
            (fun fv ->
               let uu___1 =
                 let uu___2 = PulseSyntaxWrapper.pat_cons fv [] r in
                 (uu___2, []) in
               return uu___1)
      | FStar_Parser_AST.PatApp
          ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName lid;
             FStar_Parser_AST.prange = uu___;_},
           args)
          ->
          let uu___1 = desugar_datacon env lid in
          op_let_Question uu___1
            (fun fv ->
               let uu___2 =
                 map_err
                   (fun p1 ->
                      match p1.FStar_Parser_AST.pat with
                      | FStar_Parser_AST.PatVar (id, uu___3, uu___4) ->
                          return id
                      | FStar_Parser_AST.PatWild uu___3 ->
                          let uu___4 = FStar_Ident.mk_ident ("_", r) in
                          return uu___4
                      | uu___3 ->
                          fail "invalid pattern: no deep patterns allowed" r)
                   args in
               op_let_Question uu___2
                 (fun idents ->
                    let strs =
                      FStar_Compiler_List.map FStar_Ident.string_of_id idents in
                    let pats =
                      FStar_Compiler_List.map
                        (fun s -> PulseSyntaxWrapper.pat_var s r) strs in
                    let uu___3 =
                      let uu___4 = PulseSyntaxWrapper.pat_cons fv pats r in
                      (uu___4, idents) in
                    return uu___3))
      | uu___ -> fail "invalid pattern" r
and (desugar_bind :
  env_t ->
    PulseSugar.stmt'__LetBinding__payload ->
      PulseSugar.stmt ->
        FStar_Compiler_Range_Type.range -> PulseSyntaxWrapper.st_term err)
  =
  fun env ->
    fun lb ->
      fun s2 ->
        fun r ->
          let uu___ = desugar_term_opt env lb.PulseSugar.typ in
          op_let_Question uu___
            (fun annot ->
               let uu___1 =
                 let uu___2 = push_bv env lb.PulseSugar.id in
                 match uu___2 with
                 | (env1, bv) ->
                     let uu___3 = desugar_stmt env1 s2 in
                     op_let_Question uu___3
                       (fun s21 ->
                          let uu___4 =
                            PulseSyntaxWrapper.close_st_term s21
                              bv.FStar_Syntax_Syntax.index in
                          return uu___4) in
               op_let_Question uu___1
                 (fun s21 ->
                    match lb.PulseSugar.init1 with
                    | FStar_Pervasives_Native.None ->
                        failwith
                          "Uninitialized variables are not yet handled"
                    | FStar_Pervasives_Native.Some e1 ->
                        (match lb.PulseSugar.qualifier with
                         | FStar_Pervasives_Native.None ->
                             (if PulseSugar.uu___is_Array_initializer e1
                              then
                                failwith
                                  "immutable local arrays are not yet supported"
                              else ();
                              (let uu___3 = e1 in
                               match uu___3 with
                               | PulseSugar.Default_initializer e11 ->
                                   let uu___4 = tosyntax env e11 in
                                   op_let_Question uu___4
                                     (fun s1 ->
                                        let b =
                                          PulseSyntaxWrapper.mk_binder
                                            lb.PulseSugar.id annot in
                                        let t =
                                          let uu___5 = admit_or_return env s1 in
                                          match uu___5 with
                                          | STTerm s11 -> mk_bind b s11 s21 r
                                          | Return s11 ->
                                              let uu___6 = as_term s11 in
                                              mk_totbind b uu___6 s21 r in
                                        return t)))
                         | FStar_Pervasives_Native.Some (PulseSugar.MUT) ->
                             let b =
                               PulseSyntaxWrapper.mk_binder lb.PulseSugar.id
                                 annot in
                             (match e1 with
                              | PulseSugar.Array_initializer
                                  { PulseSugar.init = init;
                                    PulseSugar.len = len;_}
                                  ->
                                  let uu___2 = desugar_term env init in
                                  op_let_Question uu___2
                                    (fun init1 ->
                                       let uu___3 = desugar_term env len in
                                       op_let_Question uu___3
                                         (fun len1 ->
                                            let uu___4 =
                                              PulseSyntaxWrapper.tm_let_mut_array
                                                b init1 len1 s21 r in
                                            return uu___4))
                              | PulseSugar.Default_initializer e11 ->
                                  let uu___2 = desugar_term env e11 in
                                  op_let_Question uu___2
                                    (fun e12 ->
                                       let uu___3 =
                                         PulseSyntaxWrapper.tm_let_mut b e12
                                           s21 r in
                                       return uu___3))
                         | FStar_Pervasives_Native.Some (PulseSugar.REF) ->
                             let b =
                               PulseSyntaxWrapper.mk_binder lb.PulseSugar.id
                                 annot in
                             (match e1 with
                              | PulseSugar.Array_initializer
                                  { PulseSugar.init = init;
                                    PulseSugar.len = len;_}
                                  ->
                                  let uu___2 = desugar_term env init in
                                  op_let_Question uu___2
                                    (fun init1 ->
                                       let uu___3 = desugar_term env len in
                                       op_let_Question uu___3
                                         (fun len1 ->
                                            let uu___4 =
                                              PulseSyntaxWrapper.tm_let_mut_array
                                                b init1 len1 s21 r in
                                            return uu___4))
                              | PulseSugar.Default_initializer e11 ->
                                  let uu___2 = desugar_term env e11 in
                                  op_let_Question uu___2
                                    (fun e12 ->
                                       let uu___3 =
                                         PulseSyntaxWrapper.tm_let_mut b e12
                                           s21 r in
                                       return uu___3)))))
and (desugar_sequence :
  env_t ->
    PulseSugar.stmt ->
      PulseSugar.stmt -> PulseSugar.rng -> PulseSyntaxWrapper.st_term err)
  =
  fun env ->
    fun s1 ->
      fun s2 ->
        fun r ->
          let uu___ = desugar_stmt env s1 in
          op_let_Question uu___
            (fun s11 ->
               let uu___1 = desugar_stmt env s2 in
               op_let_Question uu___1
                 (fun s21 ->
                    let annot =
                      let uu___2 = FStar_Ident.id_of_text "_" in
                      let uu___3 = PulseSyntaxWrapper.tm_unknown r in
                      PulseSyntaxWrapper.mk_binder uu___2 uu___3 in
                    let uu___2 = mk_bind annot s11 s21 r in return uu___2))
and (desugar_proof_hint_with_binders :
  env_t ->
    PulseSugar.stmt ->
      PulseSugar.stmt FStar_Pervasives_Native.option ->
        PulseSugar.rng -> PulseSyntaxWrapper.st_term err)
  =
  fun env ->
    fun s1 ->
      fun k ->
        fun r ->
          match s1.PulseSugar.s with
          | PulseSugar.ProofHintWithBinders
              { PulseSugar.hint_type = hint_type; PulseSugar.binders1 = bs;_}
              ->
              let uu___ = desugar_binders env bs in
              op_let_Question uu___
                (fun uu___1 ->
                   match uu___1 with
                   | (env1, binders, bvs) ->
                       let vars =
                         FStar_Compiler_List.map
                           (fun bv -> bv.FStar_Syntax_Syntax.index) bvs in
                       let uu___2 = desugar_hint_type env1 hint_type in
                       op_let_Question uu___2
                         (fun ht ->
                            let uu___3 =
                              match k with
                              | FStar_Pervasives_Native.None ->
                                  let uu___4 =
                                    let uu___5 =
                                      PulseSyntaxWrapper.tm_expr
                                        FStar_Syntax_Syntax.unit_const r in
                                    PulseSyntaxWrapper.tm_ghost_return uu___5
                                      r in
                                  return uu___4
                              | FStar_Pervasives_Native.Some s2 ->
                                  desugar_stmt env1 s2 in
                            op_let_Question uu___3
                              (fun s2 ->
                                 let binders1 =
                                   FStar_Compiler_List.map
                                     FStar_Pervasives_Native.snd binders in
                                 let sub =
                                   PulseSyntaxWrapper.bvs_as_subst vars in
                                 let s21 =
                                   PulseSyntaxWrapper.subst_st_term sub s2 in
                                 let ht1 =
                                   PulseSyntaxWrapper.subst_proof_hint sub ht in
                                 let uu___4 =
                                   let uu___5 =
                                     PulseSyntaxWrapper.close_binders
                                       binders1 vars in
                                   PulseSyntaxWrapper.tm_proof_hint_with_binders
                                     ht1 uu___5 s21 r in
                                 return uu___4)))
          | uu___ ->
              fail "Expected ProofHintWithBinders" s1.PulseSugar.range1
and (desugar_binders :
  env_t ->
    PulseSugar.binders ->
      (env_t * (PulseSyntaxWrapper.qualifier FStar_Pervasives_Native.option *
        PulseSyntaxWrapper.binder) Prims.list * FStar_Syntax_Syntax.bv
        Prims.list) err)
  =
  fun env ->
    fun bs ->
      let rec aux env1 bs1 =
        match bs1 with
        | [] -> return (env1, [], [])
        | (aq, b, t)::bs2 ->
            let uu___ = desugar_term env1 t in
            op_let_Question uu___
              (fun t1 ->
                 let uu___1 = push_bv env1 b in
                 match uu___1 with
                 | (env2, bv) ->
                     let uu___2 = aux env2 bs2 in
                     op_let_Question uu___2
                       (fun uu___3 ->
                          match uu___3 with
                          | (env3, bs3, bvs) ->
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 = as_qual aq in
                                    (uu___7, b, t1) in
                                  uu___6 :: bs3 in
                                (env3, uu___5, (bv :: bvs)) in
                              return uu___4)) in
      let uu___ = aux env bs in
      op_let_Question uu___
        (fun uu___1 ->
           match uu___1 with
           | (env1, bs1, bvs) ->
               let uu___2 =
                 let uu___3 =
                   FStar_Compiler_List.map
                     (fun uu___4 ->
                        match uu___4 with
                        | (aq, b, t) ->
                            let uu___5 = PulseSyntaxWrapper.mk_binder b t in
                            (aq, uu___5)) bs1 in
                 (env1, uu___3, bvs) in
               return uu___2)
let rec fold_right1 : 'a . ('a -> 'a -> 'a) -> 'a Prims.list -> 'a =
  fun f ->
    fun l ->
      match l with
      | h::[] -> h
      | h::t -> let uu___ = fold_right1 f t in f h uu___
let (desugar_computation_type :
  env_t -> PulseSugar.computation_type -> PulseSyntaxWrapper.comp err) =
  fun env ->
    fun c ->
      let uu___ = desugar_vprop env c.PulseSugar.precondition in
      op_let_Question uu___
        (fun pre ->
           let uu___1 = desugar_term env c.PulseSugar.return_type in
           op_let_Question uu___1
             (fun ret1 ->
                let uu___2 =
                  match c.PulseSugar.opens with
                  | FStar_Pervasives_Native.Some t -> desugar_term env t
                  | FStar_Pervasives_Native.None ->
                      return PulseSyntaxWrapper.tm_emp_inames in
                op_let_Question uu___2
                  (fun opens ->
                     let uu___3 = push_bv env c.PulseSugar.return_name in
                     match uu___3 with
                     | (env1, bv) ->
                         let uu___4 =
                           desugar_vprop env1 c.PulseSugar.postcondition in
                         op_let_Question uu___4
                           (fun post ->
                              let post1 =
                                PulseSyntaxWrapper.close_term post
                                  bv.FStar_Syntax_Syntax.index in
                              match c.PulseSugar.tag with
                              | PulseSugar.ST ->
                                  let uu___5 =
                                    if
                                      FStar_Pervasives_Native.uu___is_Some
                                        c.PulseSugar.opens
                                    then
                                      fail
                                        "STT computations are not indexed by invariants. Either remove the `opens` or make this function ghost/atomic."
                                        (FStar_Pervasives_Native.__proj__Some__item__v
                                           c.PulseSugar.opens).FStar_Parser_AST.range
                                    else return () in
                                  op_let_Question uu___5
                                    (fun uu___6 ->
                                       let uu___7 =
                                         let uu___8 =
                                           PulseSyntaxWrapper.mk_binder
                                             c.PulseSugar.return_name ret1 in
                                         PulseSyntaxWrapper.mk_comp pre
                                           uu___8 post1 in
                                       return uu___7)
                              | PulseSugar.STAtomic ->
                                  let uu___5 =
                                    let uu___6 =
                                      PulseSyntaxWrapper.mk_binder
                                        c.PulseSugar.return_name ret1 in
                                    PulseSyntaxWrapper.atomic_comp opens pre
                                      uu___6 post1 in
                                  return uu___5
                              | PulseSugar.STGhost ->
                                  let uu___5 =
                                    let uu___6 =
                                      PulseSyntaxWrapper.mk_binder
                                        c.PulseSugar.return_name ret1 in
                                    PulseSyntaxWrapper.ghost_comp opens pre
                                      uu___6 post1 in
                                  return uu___5))))
let rec (free_vars_term :
  env_t -> FStar_Parser_AST.term -> FStar_Ident.ident Prims.list) =
  fun env ->
    fun t ->
      FStar_ToSyntax_ToSyntax.free_vars false
        (env.tcenv).FStar_TypeChecker_Env.dsenv t
and (free_vars_vprop :
  env_t -> PulseSugar.vprop -> FStar_Ident.ident Prims.list) =
  fun env ->
    fun t ->
      match t.PulseSugar.v with
      | PulseSugar.VPropTerm t1 -> free_vars_term env t1
      | PulseSugar.VPropStar (t0, t1) ->
          let uu___ = free_vars_vprop env t0 in
          let uu___1 = free_vars_vprop env t1 in
          FStar_List_Tot_Base.op_At uu___ uu___1
      | PulseSugar.VPropExists
          { PulseSugar.binders = binders; PulseSugar.body = body;_} ->
          let uu___ = free_vars_binders env binders in
          (match uu___ with
           | (env', fvs) ->
               let uu___1 = free_vars_vprop env' body in
               FStar_List_Tot_Base.op_At fvs uu___1)
and (free_vars_binders :
  env_t -> PulseSugar.binders -> (env_t * FStar_Ident.ident Prims.list)) =
  fun env ->
    fun bs ->
      match bs with
      | [] -> (env, [])
      | (uu___, x, t)::bs1 ->
          let fvs = free_vars_term env t in
          let uu___1 =
            let uu___2 =
              let uu___3 = push_bv env x in
              FStar_Pervasives_Native.fst uu___3 in
            free_vars_binders uu___2 bs1 in
          (match uu___1 with
           | (env', res) -> (env', (FStar_List_Tot_Base.op_At fvs res)))
let free_vars_list :
  'a .
    (env_t -> 'a -> FStar_Ident.ident Prims.list) ->
      env_t -> 'a Prims.list -> FStar_Ident.ident Prims.list
  = fun f -> fun env -> fun xs -> FStar_Compiler_List.collect (f env) xs
let (free_vars_comp :
  env_t -> PulseSugar.computation_type -> FStar_Ident.ident Prims.list) =
  fun env ->
    fun c ->
      let ids =
        let uu___ = free_vars_vprop env c.PulseSugar.precondition in
        let uu___1 =
          let uu___2 = free_vars_term env c.PulseSugar.return_type in
          let uu___3 =
            let uu___4 =
              let uu___5 = push_bv env c.PulseSugar.return_name in
              FStar_Pervasives_Native.fst uu___5 in
            free_vars_vprop uu___4 c.PulseSugar.postcondition in
          FStar_List_Tot_Base.op_At uu___2 uu___3 in
        FStar_List_Tot_Base.op_At uu___ uu___1 in
      FStar_Compiler_List.deduplicate FStar_Ident.ident_equals ids
let (idents_as_binders :
  env_t ->
    FStar_Ident.ident Prims.list ->
      (env_t * (PulseSyntaxWrapper.qualifier FStar_Pervasives_Native.option *
        PulseSyntaxWrapper.binder) Prims.list * FStar_Syntax_Syntax.bv
        Prims.list) err)
  =
  fun env ->
    fun l ->
      let erased_tm =
        FStar_Parser_AST.mk_term
          (FStar_Parser_AST.Var FStar_Parser_Const.erased_lid)
          FStar_Compiler_Range_Type.dummyRange FStar_Parser_AST.Un in
      let rec aux env1 binders bvs l1 =
        match l1 with
        | [] ->
            return
              (env1, (FStar_Compiler_List.rev binders),
                (FStar_Compiler_List.rev bvs))
        | i::l2 ->
            let uu___ = push_bv env1 i in
            (match uu___ with
             | (env2, bv) ->
                 let qual1 = PulseSyntaxWrapper.as_qual true in
                 let text = FStar_Ident.string_of_id i in
                 let wild =
                   let uu___1 = FStar_Ident.range_of_id i in
                   FStar_Parser_AST.mk_term FStar_Parser_AST.Wild uu___1
                     FStar_Parser_AST.Un in
                 let ty =
                   if FStar_Compiler_Util.starts_with text "'"
                   then
                     let uu___1 = FStar_Ident.range_of_id i in
                     FStar_Parser_AST.mkApp erased_tm
                       [(wild, FStar_Parser_AST.Nothing)] uu___1
                   else wild in
                 let uu___1 = desugar_term env2 ty in
                 op_let_Question uu___1
                   (fun ty1 ->
                      let uu___2 =
                        let uu___3 =
                          let uu___4 = PulseSyntaxWrapper.mk_binder i ty1 in
                          (qual1, uu___4) in
                        uu___3 :: binders in
                      aux env2 uu___2 (bv :: bvs) l2)) in
      aux env [] [] l
type mutvar_entry =
  (FStar_Ident.ident * FStar_Syntax_Syntax.bv * FStar_Ident.ident
    FStar_Pervasives_Native.option)
type menv = {
  map: mutvar_entry Prims.list ;
  env: env_t }
let (__proj__Mkmenv__item__map : menv -> mutvar_entry Prims.list) =
  fun projectee -> match projectee with | { map; env;_} -> map
let (__proj__Mkmenv__item__env : menv -> env_t) =
  fun projectee -> match projectee with | { map; env;_} -> env
let (menv_push_ns : menv -> FStar_Ident.lid -> menv) =
  fun m ->
    fun ns ->
      let uu___ = push_namespace m.env ns in { map = (m.map); env = uu___ }
let (menv_push_bv :
  menv ->
    FStar_Ident.ident ->
      PulseSugar.mut_or_ref FStar_Pervasives_Native.option ->
        Prims.bool -> menv)
  =
  fun m ->
    fun x ->
      fun q ->
        fun auto_deref_applicable ->
          let uu___ = push_bv m.env x in
          match uu___ with
          | (env, bv) ->
              let m1 = { map = (m.map); env } in
              if
                (q = (FStar_Pervasives_Native.Some PulseSugar.MUT)) &&
                  auto_deref_applicable
              then
                {
                  map = ((x, bv, FStar_Pervasives_Native.None) :: (m1.map));
                  env = (m1.env)
                }
              else m1
let (menv_push_bvs : menv -> FStar_Ident.ident Prims.list -> menv) =
  fun m ->
    fun xs ->
      let uu___ =
        let uu___1 = push_bvs m.env xs in FStar_Pervasives_Native.fst uu___1 in
      { map = (m.map); env = uu___ }
let (is_mut :
  menv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Ident.ident FStar_Pervasives_Native.option
        FStar_Pervasives_Native.option)
  =
  fun m ->
    fun x ->
      let uu___ =
        FStar_Compiler_List.tryFind
          (fun uu___1 ->
             match uu___1 with
             | (uu___2, y, uu___3) -> FStar_Syntax_Syntax.bv_eq x y) 
          m.map in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu___1, uu___2, curval) ->
          FStar_Pervasives_Native.Some curval
type needs_derefs = (FStar_Ident.ident * FStar_Ident.ident) Prims.list
let (fresh_var : FStar_Ident.ident -> FStar_Ident.ident err) =
  fun nm ->
    op_let_Question next_ctr
      (fun ctr ->
         let s =
           let uu___ = FStar_Ident.string_of_id nm in
           Prims.op_Hat uu___ (Prims.op_Hat "@" (Prims.string_of_int ctr)) in
         let uu___ =
           let uu___1 =
             let uu___2 = FStar_Ident.range_of_id nm in (s, uu___2) in
           FStar_Ident.mk_ident uu___1 in
         return uu___)
let (bind_curval : menv -> FStar_Ident.ident -> FStar_Ident.ident -> menv) =
  fun m ->
    fun x ->
      fun curval ->
        let uu___ =
          FStar_Compiler_List.tryFind
            (fun uu___1 ->
               match uu___1 with
               | (y, uu___2, uu___3) -> FStar_Ident.ident_equals x y) 
            m.map in
        match uu___ with
        | FStar_Pervasives_Native.None -> failwith "Impossible 1"
        | FStar_Pervasives_Native.Some (x1, bv, uu___1) ->
            {
              map = ((x1, bv, (FStar_Pervasives_Native.Some curval)) ::
                (m.map));
              env = (m.env)
            }
let (clear_curval : menv -> FStar_Ident.ident -> menv) =
  fun m ->
    fun x ->
      let uu___ =
        FStar_Compiler_List.tryFind
          (fun uu___1 ->
             match uu___1 with
             | (y, uu___2, uu___3) -> FStar_Ident.ident_equals x y) m.map in
      match uu___ with
      | FStar_Pervasives_Native.None -> failwith "Impossible 2"
      | FStar_Pervasives_Native.Some (x1, bv, uu___1) ->
          {
            map = ((x1, bv, FStar_Pervasives_Native.None) :: (m.map));
            env = (m.env)
          }
let (bind_curvals : menv -> needs_derefs -> menv) =
  fun m ->
    fun l ->
      FStar_Compiler_List.fold_left
        (fun m1 ->
           fun uu___ -> match uu___ with | (x, y) -> bind_curval m1 x y) m l
let (resolve_mut :
  menv ->
    FStar_Parser_AST.term -> mutvar_entry FStar_Pervasives_Native.option)
  =
  fun m ->
    fun e ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var l ->
          let topt =
            FStar_Syntax_DsEnv.try_lookup_lid
              ((m.env).tcenv).FStar_TypeChecker_Env.dsenv l in
          (match topt with
           | FStar_Pervasives_Native.Some
               { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name x;
                 FStar_Syntax_Syntax.pos = uu___;
                 FStar_Syntax_Syntax.vars = uu___1;
                 FStar_Syntax_Syntax.hash_code = uu___2;_}
               ->
               FStar_Compiler_List.tryFind
                 (fun uu___3 ->
                    match uu___3 with
                    | (uu___4, y, uu___5) -> FStar_Syntax_Syntax.bv_eq x y)
                 m.map
           | uu___ -> FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None
let (maybe_clear_curval : menv -> FStar_Parser_AST.term -> menv) =
  fun m ->
    fun x ->
      let uu___ = resolve_mut m x in
      match uu___ with
      | FStar_Pervasives_Native.None -> m
      | FStar_Pervasives_Native.Some (x1, y, uu___1) ->
          {
            map = ((x1, y, FStar_Pervasives_Native.None) :: (m.map));
            env = (m.env)
          }
let (add_derefs_in_scope :
  needs_derefs -> PulseSugar.stmt -> PulseSugar.stmt) =
  fun n ->
    fun p ->
      FStar_Compiler_List.fold_right
        (fun uu___ ->
           fun p1 ->
             match uu___ with
             | (x, y) ->
                 let lb =
                   let uu___1 =
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 = read x in
                           PulseSugar.Default_initializer uu___5 in
                         FStar_Pervasives_Native.Some uu___4 in
                       {
                         PulseSugar.qualifier = FStar_Pervasives_Native.None;
                         PulseSugar.id = y;
                         PulseSugar.typ = FStar_Pervasives_Native.None;
                         PulseSugar.init1 = uu___3
                       } in
                     PulseSugar.LetBinding uu___2 in
                   {
                     PulseSugar.s = uu___1;
                     PulseSugar.range1 = (p1.PulseSugar.range1)
                   } in
                 {
                   PulseSugar.s =
                     (PulseSugar.Sequence
                        { PulseSugar.s1 = lb; PulseSugar.s2 = p1 });
                   PulseSugar.range1 = (p1.PulseSugar.range1)
                 }) n p
let (term'_of_id : FStar_Ident.ident -> FStar_Parser_AST.term') =
  fun y ->
    let uu___ = FStar_Ident.lid_of_ids [y] in FStar_Parser_AST.Var uu___
let rec (transform_term :
  menv ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.term * needs_derefs * menv) err)
  =
  fun m ->
    fun e ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var uu___ ->
          let uu___1 = resolve_mut m e in
          (match uu___1 with
           | FStar_Pervasives_Native.None -> return (e, [], m)
           | FStar_Pervasives_Native.Some
               (x, uu___2, FStar_Pervasives_Native.None) ->
               let uu___3 = fresh_var x in
               op_let_Question uu___3
                 (fun y ->
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = FStar_Ident.lid_of_ids [y] in
                          FStar_Parser_AST.Var uu___7 in
                        {
                          FStar_Parser_AST.tm = uu___6;
                          FStar_Parser_AST.range = (e.FStar_Parser_AST.range);
                          FStar_Parser_AST.level = (e.FStar_Parser_AST.level)
                        } in
                      let uu___6 = bind_curval m x y in
                      (uu___5, [(x, y)], uu___6) in
                    return uu___4)
           | FStar_Pervasives_Native.Some
               (uu___2, uu___3, FStar_Pervasives_Native.Some y) ->
               let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     let uu___7 = FStar_Ident.lid_of_ids [y] in
                     FStar_Parser_AST.Var uu___7 in
                   {
                     FStar_Parser_AST.tm = uu___6;
                     FStar_Parser_AST.range = (e.FStar_Parser_AST.range);
                     FStar_Parser_AST.level = (e.FStar_Parser_AST.level)
                   } in
                 (uu___5, [], m) in
               return uu___4)
      | FStar_Parser_AST.Op (id, tms) ->
          let uu___ =
            fold_err
              (fun uu___1 ->
                 fun tm ->
                   match uu___1 with
                   | (tms1, needs, m1) ->
                       let uu___2 = transform_term m1 tm in
                       op_let_Question uu___2
                         (fun uu___3 ->
                            match uu___3 with
                            | (tm1, needs', m') ->
                                return
                                  ((tm1 :: tms1),
                                    (FStar_List_Tot_Base.op_At needs needs'),
                                    m'))) tms ([], [], m) in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (tms1, needs, m1) ->
                   let e1 =
                     {
                       FStar_Parser_AST.tm =
                         (FStar_Parser_AST.Op
                            (id, (FStar_Compiler_List.rev tms1)));
                       FStar_Parser_AST.range = (e.FStar_Parser_AST.range);
                       FStar_Parser_AST.level = (e.FStar_Parser_AST.level)
                     } in
                   return (e1, needs, m1))
      | FStar_Parser_AST.App (head, arg, imp) ->
          let uu___ = transform_term m head in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (head1, needs, m1) ->
                   let uu___2 = transform_term m1 arg in
                   op_let_Question uu___2
                     (fun uu___3 ->
                        match uu___3 with
                        | (arg1, needs', m2) ->
                            let e1 =
                              {
                                FStar_Parser_AST.tm =
                                  (FStar_Parser_AST.App (head1, arg1, imp));
                                FStar_Parser_AST.range =
                                  (e.FStar_Parser_AST.range);
                                FStar_Parser_AST.level =
                                  (e.FStar_Parser_AST.level)
                              } in
                            return
                              (e1, (FStar_List_Tot_Base.op_At needs needs'),
                                m2)))
      | FStar_Parser_AST.Ascribed (e1, t, topt, b) ->
          let uu___ = transform_term m e1 in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (e2, needs, m1) ->
                   let e3 =
                     {
                       FStar_Parser_AST.tm =
                         (FStar_Parser_AST.Ascribed (e2, t, topt, b));
                       FStar_Parser_AST.range = (e2.FStar_Parser_AST.range);
                       FStar_Parser_AST.level = (e2.FStar_Parser_AST.level)
                     } in
                   return (e3, needs, m1))
      | FStar_Parser_AST.Paren e1 ->
          let uu___ = transform_term m e1 in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (e2, needs, m1) ->
                   let e3 =
                     {
                       FStar_Parser_AST.tm = (FStar_Parser_AST.Paren e2);
                       FStar_Parser_AST.range = (e2.FStar_Parser_AST.range);
                       FStar_Parser_AST.level = (e2.FStar_Parser_AST.level)
                     } in
                   return (e3, needs, m1))
      | FStar_Parser_AST.Construct (lid, tms) ->
          let uu___ =
            fold_err
              (fun uu___1 ->
                 fun uu___2 ->
                   match (uu___1, uu___2) with
                   | ((tms1, needs, m1), (tm, imp)) ->
                       let uu___3 = transform_term m1 tm in
                       op_let_Question uu___3
                         (fun uu___4 ->
                            match uu___4 with
                            | (tm1, needs', m') ->
                                return
                                  (((tm1, imp) :: tms1),
                                    (FStar_List_Tot_Base.op_At needs needs'),
                                    m'))) tms ([], [], m) in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (tms1, needs, m1) ->
                   let e1 =
                     {
                       FStar_Parser_AST.tm =
                         (FStar_Parser_AST.Construct
                            (lid, (FStar_Compiler_List.rev tms1)));
                       FStar_Parser_AST.range = (e.FStar_Parser_AST.range);
                       FStar_Parser_AST.level = (e.FStar_Parser_AST.level)
                     } in
                   return (e1, needs, m1))
      | FStar_Parser_AST.LetOpen (l, t) ->
          let m1 = menv_push_ns m l in
          let uu___ = transform_term m1 t in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (p, needs, uu___2) ->
                   let uu___3 =
                     let uu___4 = bind_curvals m1 needs in (p, needs, uu___4) in
                   return uu___3)
      | uu___ -> return (e, [], m)
let rec (transform_stmt_with_reads :
  menv -> PulseSugar.stmt -> (PulseSugar.stmt * needs_derefs * menv) err) =
  fun m ->
    fun p ->
      match p.PulseSugar.s with
      | PulseSugar.Sequence { PulseSugar.s1 = s1; PulseSugar.s2 = s2;_} ->
          let uu___ = transform_stmt_with_reads m s1 in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (s11, needs, m1) ->
                   let uu___2 = transform_stmt m1 s2 in
                   op_let_Question uu___2
                     (fun s21 ->
                        let p1 =
                          {
                            PulseSugar.s =
                              (PulseSugar.Sequence
                                 { PulseSugar.s1 = s11; PulseSugar.s2 = s21 });
                            PulseSugar.range1 = (p.PulseSugar.range1)
                          } in
                        return (p1, needs, m1)))
      | PulseSugar.Open l ->
          let uu___ = let uu___1 = menv_push_ns m l in (p, [], uu___1) in
          return uu___
      | PulseSugar.Expr { PulseSugar.e = e;_} ->
          let uu___ = transform_term m e in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (e1, needs, uu___2) ->
                   let p1 =
                     {
                       PulseSugar.s = (PulseSugar.Expr { PulseSugar.e = e1 });
                       PulseSugar.range1 = (p.PulseSugar.range1)
                     } in
                   return (p1, needs, m))
      | PulseSugar.Assignment
          { PulseSugar.lhs = lhs; PulseSugar.value = value;_} ->
          let uu___ = transform_term m value in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (value1, needs, m1) ->
                   let m2 = maybe_clear_curval m1 lhs in
                   let s1 =
                     {
                       PulseSugar.s =
                         (PulseSugar.Assignment
                            { PulseSugar.lhs = lhs; PulseSugar.value = value1
                            });
                       PulseSugar.range1 = (p.PulseSugar.range1)
                     } in
                   return (s1, needs, m2))
      | PulseSugar.ArrayAssignment
          { PulseSugar.arr = arr; PulseSugar.index = index;
            PulseSugar.value1 = value;_}
          ->
          let uu___ = transform_term m arr in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (arr1, arr_needs, m1) ->
                   let uu___2 = transform_term m1 index in
                   op_let_Question uu___2
                     (fun uu___3 ->
                        match uu___3 with
                        | (index1, index_needs, m2) ->
                            let uu___4 = transform_term m2 value in
                            op_let_Question uu___4
                              (fun uu___5 ->
                                 match uu___5 with
                                 | (value1, value_needs, m3) ->
                                     let p1 =
                                       {
                                         PulseSugar.s =
                                           (PulseSugar.ArrayAssignment
                                              {
                                                PulseSugar.arr = arr1;
                                                PulseSugar.index = index1;
                                                PulseSugar.value1 = value1
                                              });
                                         PulseSugar.range1 =
                                           (p.PulseSugar.range1)
                                       } in
                                     return
                                       (p1,
                                         (FStar_List_Tot_Base.op_At arr_needs
                                            (FStar_List_Tot_Base.op_At
                                               index_needs value_needs)), m3))))
      | PulseSugar.LetBinding
          { PulseSugar.qualifier = qualifier; PulseSugar.id = id;
            PulseSugar.typ = typ; PulseSugar.init1 = init;_}
          ->
          let uu___ =
            match init with
            | FStar_Pervasives_Native.None ->
                return (FStar_Pervasives_Native.None, [], m)
            | FStar_Pervasives_Native.Some (PulseSugar.Default_initializer e)
                ->
                let mk_init e1 =
                  FStar_Pervasives_Native.Some
                    (PulseSugar.Default_initializer e1) in
                (match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Var zlid ->
                     let uu___1 =
                       let uu___2 = FStar_Ident.ids_of_lid zlid in
                       (qualifier, uu___2) in
                     (match uu___1 with
                      | (FStar_Pervasives_Native.None, z::[]) ->
                          let uu___2 = resolve_mut m e in
                          (match uu___2 with
                           | FStar_Pervasives_Native.None ->
                               return ((mk_init e), [], m)
                           | FStar_Pervasives_Native.Some
                               (uu___3, uu___4, FStar_Pervasives_Native.Some
                                y)
                               ->
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 =
                                     let uu___8 = term'_of_id y in
                                     {
                                       FStar_Parser_AST.tm = uu___8;
                                       FStar_Parser_AST.range =
                                         (e.FStar_Parser_AST.range);
                                       FStar_Parser_AST.level =
                                         (e.FStar_Parser_AST.level)
                                     } in
                                   mk_init uu___7 in
                                 (uu___6, [], m) in
                               return uu___5
                           | FStar_Pervasives_Native.Some
                               (x, uu___3, FStar_Pervasives_Native.None) ->
                               let uu___4 =
                                 let uu___5 =
                                   let uu___6 = read x in mk_init uu___6 in
                                 let uu___6 = bind_curval m x z in
                                 (uu___5, [], uu___6) in
                               return uu___4)
                      | uu___2 ->
                          let uu___3 = transform_term m e in
                          op_let_Question uu___3
                            (fun uu___4 ->
                               match uu___4 with
                               | (init1, needs, m1) ->
                                   return ((mk_init init1), needs, m1)))
                 | uu___1 ->
                     let uu___2 = transform_term m e in
                     op_let_Question uu___2
                       (fun uu___3 ->
                          match uu___3 with
                          | (init1, needs, m1) ->
                              return ((mk_init init1), needs, m1)))
            | FStar_Pervasives_Native.Some (PulseSugar.Array_initializer
                { PulseSugar.init = init1; PulseSugar.len = len;_}) ->
                let uu___1 = transform_term m init1 in
                op_let_Question uu___1
                  (fun uu___2 ->
                     match uu___2 with
                     | (init2, needs, m1) ->
                         let uu___3 = transform_term m1 len in
                         op_let_Question uu___3
                           (fun uu___4 ->
                              match uu___4 with
                              | (len1, len_needs, m2) ->
                                  return
                                    ((FStar_Pervasives_Native.Some
                                        (PulseSugar.Array_initializer
                                           {
                                             PulseSugar.init = init2;
                                             PulseSugar.len = len1
                                           })),
                                      (FStar_List_Tot_Base.op_At needs
                                         len_needs), m2))) in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (init1, needs, m1) ->
                   let auto_deref_applicable =
                     match init1 with
                     | FStar_Pervasives_Native.Some
                         (PulseSugar.Array_initializer uu___2) -> false
                     | uu___2 -> true in
                   let m2 =
                     menv_push_bv m1 id qualifier auto_deref_applicable in
                   let p1 =
                     {
                       PulseSugar.s =
                         (PulseSugar.LetBinding
                            {
                              PulseSugar.qualifier = qualifier;
                              PulseSugar.id = id;
                              PulseSugar.typ = typ;
                              PulseSugar.init1 = init1
                            });
                       PulseSugar.range1 = (p.PulseSugar.range1)
                     } in
                   return (p1, needs, m2))
      | PulseSugar.Block { PulseSugar.stmt = stmt;_} ->
          let uu___ = transform_stmt m stmt in
          op_let_Question uu___
            (fun stmt1 ->
               let p1 =
                 {
                   PulseSugar.s =
                     (PulseSugar.Block { PulseSugar.stmt = stmt1 });
                   PulseSugar.range1 = (p.PulseSugar.range1)
                 } in
               return (p1, [], m))
      | PulseSugar.If
          { PulseSugar.head1 = head; PulseSugar.join_vprop = join_vprop;
            PulseSugar.then_ = then_; PulseSugar.else_opt = else_opt;_}
          ->
          let uu___ = transform_term m head in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (head1, needs, m1) ->
                   let uu___2 = transform_stmt m1 then_ in
                   op_let_Question uu___2
                     (fun then_1 ->
                        let uu___3 =
                          match else_opt with
                          | FStar_Pervasives_Native.None ->
                              return FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some else_ ->
                              let uu___4 = transform_stmt m1 else_ in
                              op_let_Question uu___4
                                (fun else_1 ->
                                   return
                                     (FStar_Pervasives_Native.Some else_1)) in
                        op_let_Question uu___3
                          (fun else_opt1 ->
                             let p1 =
                               {
                                 PulseSugar.s =
                                   (PulseSugar.If
                                      {
                                        PulseSugar.head1 = head1;
                                        PulseSugar.join_vprop = join_vprop;
                                        PulseSugar.then_ = then_1;
                                        PulseSugar.else_opt = else_opt1
                                      });
                                 PulseSugar.range1 = (p.PulseSugar.range1)
                               } in
                             return (p1, needs, m1))))
      | PulseSugar.Match
          { PulseSugar.head2 = head;
            PulseSugar.returns_annot = returns_annot;
            PulseSugar.branches = branches;_}
          ->
          let uu___ = transform_term m head in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (head1, needs, m1) ->
                   let uu___2 =
                     map_err
                       (fun uu___3 ->
                          match uu___3 with
                          | (p1, s) ->
                              let uu___4 = desugar_pat m1.env p1 in
                              op_let_Question uu___4
                                (fun uu___5 ->
                                   match uu___5 with
                                   | (uu___6, vs) ->
                                       let m2 = menv_push_bvs m1 vs in
                                       let uu___7 = transform_stmt m2 s in
                                       op_let_Question uu___7
                                         (fun s1 -> return (p1, s1))))
                       branches in
                   op_let_Question uu___2
                     (fun branches1 ->
                        let p1 =
                          {
                            PulseSugar.s =
                              (PulseSugar.Match
                                 {
                                   PulseSugar.head2 = head1;
                                   PulseSugar.returns_annot = returns_annot;
                                   PulseSugar.branches = branches1
                                 });
                            PulseSugar.range1 = (p.PulseSugar.range1)
                          } in
                        return (p1, needs, m1)))
      | PulseSugar.While
          { PulseSugar.guard = guard; PulseSugar.id1 = id;
            PulseSugar.invariant = invariant; PulseSugar.body1 = body;_}
          ->
          let uu___ = transform_stmt m guard in
          op_let_Question uu___
            (fun guard1 ->
               let uu___1 = transform_stmt m body in
               op_let_Question uu___1
                 (fun body1 ->
                    let p1 =
                      {
                        PulseSugar.s =
                          (PulseSugar.While
                             {
                               PulseSugar.guard = guard1;
                               PulseSugar.id1 = id;
                               PulseSugar.invariant = invariant;
                               PulseSugar.body1 = body1
                             });
                        PulseSugar.range1 = (p.PulseSugar.range1)
                      } in
                    return (p1, [], m)))
      | PulseSugar.Parallel
          { PulseSugar.p1 = p1; PulseSugar.p2 = p2; PulseSugar.q1 = q1;
            PulseSugar.q2 = q2; PulseSugar.b1 = b1; PulseSugar.b2 = b2;_}
          ->
          let uu___ = transform_stmt m b1 in
          op_let_Question uu___
            (fun b11 ->
               let uu___1 = transform_stmt m b2 in
               op_let_Question uu___1
                 (fun b21 ->
                    let p3 =
                      {
                        PulseSugar.s =
                          (PulseSugar.Parallel
                             {
                               PulseSugar.p1 = p1;
                               PulseSugar.p2 = p2;
                               PulseSugar.q1 = q1;
                               PulseSugar.q2 = q2;
                               PulseSugar.b1 = b11;
                               PulseSugar.b2 = b21
                             });
                        PulseSugar.range1 = (p.PulseSugar.range1)
                      } in
                    return (p3, [], m)))
      | PulseSugar.Introduce uu___ -> return (p, [], m)
      | PulseSugar.Rewrite uu___ -> return (p, [], m)
      | PulseSugar.ProofHintWithBinders uu___ -> return (p, [], m)
and (transform_stmt : menv -> PulseSugar.stmt -> PulseSugar.stmt err) =
  fun m ->
    fun p ->
      let uu___ = transform_stmt_with_reads m p in
      op_let_Question uu___
        (fun uu___1 ->
           match uu___1 with
           | (p1, needs, m1) ->
               let uu___2 = add_derefs_in_scope needs p1 in return uu___2)
let rec (vprop_to_ast_term : PulseSugar.vprop -> FStar_Parser_AST.term err) =
  fun v ->
    match v.PulseSugar.v with
    | PulseSugar.VPropTerm t -> return t
    | PulseSugar.VPropStar (v1, v2) ->
        let t =
          FStar_Parser_AST.mk_term (FStar_Parser_AST.Var star_lid)
            v.PulseSugar.vrange FStar_Parser_AST.Expr in
        let uu___ = vprop_to_ast_term v1 in
        op_let_Question uu___
          (fun vv1 ->
             let t1 =
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App (t, vv1, FStar_Parser_AST.Nothing))
                 v.PulseSugar.vrange FStar_Parser_AST.Expr in
             let uu___1 = vprop_to_ast_term v2 in
             op_let_Question uu___1
               (fun vv2 ->
                  let t2 =
                    FStar_Parser_AST.mk_term
                      (FStar_Parser_AST.App
                         (t1, vv2, FStar_Parser_AST.Nothing))
                      v.PulseSugar.vrange FStar_Parser_AST.Expr in
                  return t2))
    | PulseSugar.VPropExists
        { PulseSugar.binders = binders; PulseSugar.body = body;_} ->
        fail "IOU :(" v.PulseSugar.vrange
let (comp_to_ast_term :
  PulseSugar.computation_type -> FStar_Parser_AST.term err) =
  fun c ->
    let return_ty = c.PulseSugar.return_type in
    let r = c.PulseSugar.range in
    let head =
      match c.PulseSugar.tag with
      | PulseSugar.ST ->
          let h =
            FStar_Parser_AST.mk_term (FStar_Parser_AST.Var stt_lid) r
              FStar_Parser_AST.Expr in
          let h1 =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (h, return_ty, FStar_Parser_AST.Nothing))
              r FStar_Parser_AST.Expr in
          h1
      | PulseSugar.STAtomic ->
          let is =
            let uu___ =
              let uu___1 = FStar_Ident.lid_of_str "Pulse.Lib.Core.emp_inames" in
              FStar_Parser_AST.Var uu___1 in
            FStar_Parser_AST.mk_term uu___ r FStar_Parser_AST.Expr in
          let h =
            FStar_Parser_AST.mk_term (FStar_Parser_AST.Var stt_atomic_lid) r
              FStar_Parser_AST.Expr in
          let h1 =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (h, return_ty, FStar_Parser_AST.Nothing))
              r FStar_Parser_AST.Expr in
          FStar_Parser_AST.mk_term
            (FStar_Parser_AST.App (h1, is, FStar_Parser_AST.Nothing)) r
            FStar_Parser_AST.Expr
      | PulseSugar.STGhost ->
          let is =
            let uu___ =
              let uu___1 = FStar_Ident.lid_of_str "Pulse.Lib.Core.emp_inames" in
              FStar_Parser_AST.Var uu___1 in
            FStar_Parser_AST.mk_term uu___ r FStar_Parser_AST.Expr in
          let h =
            FStar_Parser_AST.mk_term (FStar_Parser_AST.Var stt_ghost_lid) r
              FStar_Parser_AST.Expr in
          let h1 =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (h, return_ty, FStar_Parser_AST.Nothing))
              r FStar_Parser_AST.Expr in
          FStar_Parser_AST.mk_term
            (FStar_Parser_AST.App (h1, is, FStar_Parser_AST.Nothing)) r
            FStar_Parser_AST.Expr in
    let uu___ = vprop_to_ast_term c.PulseSugar.precondition in
    op_let_Question uu___
      (fun pre ->
         let uu___1 = vprop_to_ast_term c.PulseSugar.postcondition in
         op_let_Question uu___1
           (fun post ->
              let post1 =
                let pat =
                  FStar_Parser_AST.mk_pattern
                    (FStar_Parser_AST.PatVar
                       ((c.PulseSugar.return_name),
                         FStar_Pervasives_Native.None, [])) r in
                let pat1 =
                  FStar_Parser_AST.mk_pattern
                    (FStar_Parser_AST.PatAscribed
                       (pat, (return_ty, FStar_Pervasives_Native.None))) r in
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.Abs ([pat1], post)) r
                  FStar_Parser_AST.Expr in
              let t =
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.App (head, pre, FStar_Parser_AST.Nothing))
                  r FStar_Parser_AST.Expr in
              let t1 =
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.App (t, post1, FStar_Parser_AST.Nothing))
                  r FStar_Parser_AST.Expr in
              return t1))
let rec map2 :
  'a 'b 'c .
    ('a -> 'b -> 'c) -> 'a Prims.list -> 'b Prims.list -> 'c Prims.list err
  =
  fun f ->
    fun xs ->
      fun ys ->
        match (xs, ys) with
        | ([], []) -> return []
        | (x::xx, y::yy) ->
            let uu___ = map2 f xx yy in
            op_let_Question uu___
              (fun r ->
                 let uu___1 = let uu___2 = f x y in uu___2 :: r in
                 return uu___1)
        | uu___ -> fail "map2: mismatch" r_
let (faux :
  (PulseSyntaxWrapper.qualifier FStar_Pervasives_Native.option *
    PulseSyntaxWrapper.binder) ->
    FStar_Syntax_Syntax.bv ->
      (PulseSyntaxWrapper.qualifier FStar_Pervasives_Native.option *
        PulseSyntaxWrapper.binder * PulseSyntaxWrapper.bv))
  =
  fun qb ->
    fun bv ->
      let uu___ = qb in
      match uu___ with
      | (q, b) ->
          let bv1 =
            let uu___1 =
              FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
            PulseSyntaxWrapper.mk_bv bv.FStar_Syntax_Syntax.index uu___1
              (bv.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
          (q, b, bv1)
let (mk_knot_arr :
  env_t ->
    FStar_Parser_AST.term FStar_Pervasives_Native.option ->
      PulseSugar.binders ->
        PulseSugar.computation_type -> FStar_Parser_AST.term err)
  =
  fun env ->
    fun meas ->
      fun bs ->
        fun res ->
          let r = FStar_Ident.range_of_id res.PulseSugar.return_name in
          let uu___ = desugar_binders env bs in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (env1, bs', uu___2) ->
                   let uu___3 = comp_to_ast_term res in
                   op_let_Question uu___3
                     (fun res_t ->
                        let bs'' =
                          FStar_Compiler_Effect.op_Bar_Greater bs
                            (FStar_Compiler_List.map
                               (fun uu___4 ->
                                  match uu___4 with
                                  | (q, x, ty) ->
                                      FStar_Parser_AST.mk_binder
                                        (FStar_Parser_AST.Annotated (x, ty))
                                        r FStar_Parser_AST.Expr q)) in
                        let last = FStar_Compiler_List.last bs'' in
                        let init = FStar_Compiler_List.init bs'' in
                        let bs''1 = FStar_List_Tot_Base.op_At init [last] in
                        let uu___4 =
                          FStar_Parser_AST.mk_term
                            (FStar_Parser_AST.Product (bs''1, res_t)) r
                            FStar_Parser_AST.Expr in
                        return uu___4))
let rec (desugar_decl :
  env_t -> PulseSugar.decl -> PulseSyntaxWrapper.decl err) =
  fun env ->
    fun d ->
      match d with
      | PulseSugar.FnDecl p ->
          let uu___ = desugar_binders env p.PulseSugar.binders2 in
          op_let_Question uu___
            (fun uu___1 ->
               match uu___1 with
               | (env1, bs, bvs) ->
                   let fvs = free_vars_comp env1 p.PulseSugar.ascription in
                   let uu___2 = idents_as_binders env1 fvs in
                   op_let_Question uu___2
                     (fun uu___3 ->
                        match uu___3 with
                        | (env2, bs', bvs') ->
                            let bs1 = FStar_List_Tot_Base.op_At bs bs' in
                            let bvs1 = FStar_List_Tot_Base.op_At bvs bvs' in
                            let uu___4 =
                              desugar_computation_type env2
                                p.PulseSugar.ascription in
                            op_let_Question uu___4
                              (fun comp ->
                                 let uu___5 =
                                   let uu___6 =
                                     let uu___7 =
                                       FStar_Options.ext_getv "pulse:rvalues" in
                                     uu___7 <> "" in
                                   if uu___6
                                   then
                                     transform_stmt { map = []; env = env2 }
                                       p.PulseSugar.body3
                                   else return p.PulseSugar.body3 in
                                 op_let_Question uu___5
                                   (fun body ->
                                      let uu___6 =
                                        map_err_opt (desugar_term env2)
                                          p.PulseSugar.measure in
                                      op_let_Question uu___6
                                        (fun meas ->
                                           let uu___7 =
                                             if p.PulseSugar.is_rec
                                             then
                                               let uu___8 =
                                                 mk_knot_arr env2
                                                   p.PulseSugar.measure
                                                   p.PulseSugar.binders2
                                                   p.PulseSugar.ascription in
                                               op_let_Question uu___8
                                                 (fun ty ->
                                                    let uu___9 =
                                                      desugar_term env2 ty in
                                                    op_let_Question uu___9
                                                      (fun ty1 ->
                                                         let uu___10 =
                                                           push_bv env2
                                                             p.PulseSugar.id2 in
                                                         match uu___10 with
                                                         | (env3, bv) ->
                                                             let b =
                                                               PulseSyntaxWrapper.mk_binder
                                                                 p.PulseSugar.id2
                                                                 ty1 in
                                                             return
                                                               (env3,
                                                                 (FStar_List_Tot_Base.op_At
                                                                    bs1
                                                                    [
                                                                    (FStar_Pervasives_Native.None,
                                                                    b)]),
                                                                 (FStar_List_Tot_Base.op_At
                                                                    bvs1 
                                                                    [bv]))))
                                             else return (env2, bs1, bvs1) in
                                           op_let_Question uu___7
                                             (fun uu___8 ->
                                                match uu___8 with
                                                | (env3, bs2, bvs2) ->
                                                    let uu___9 =
                                                      desugar_stmt env3 body in
                                                    op_let_Question uu___9
                                                      (fun body1 ->
                                                         let uu___10 =
                                                           map2 faux bs2 bvs2 in
                                                         op_let_Question
                                                           uu___10
                                                           (fun qbs ->
                                                              let uu___11 =
                                                                PulseSyntaxWrapper.fn_decl
                                                                  p.PulseSugar.range2
                                                                  p.PulseSugar.id2
                                                                  p.PulseSugar.is_rec
                                                                  qbs comp
                                                                  meas body1 in
                                                              return uu___11))))))))
type name = Prims.string Prims.list
let (initialize_env :
  FStar_TypeChecker_Env.env ->
    name Prims.list -> (Prims.string * name) Prims.list -> env_t)
  =
  fun env ->
    fun open_namespaces ->
      fun module_abbrevs ->
        let dsenv = env.FStar_TypeChecker_Env.dsenv in
        let dsenv1 =
          let uu___ = FStar_TypeChecker_Env.current_module env in
          FStar_Syntax_DsEnv.set_current_module dsenv uu___ in
        let dsenv2 =
          FStar_Compiler_List.fold_right
            (fun ns ->
               fun env1 ->
                 let uu___ = FStar_Ident.lid_of_path ns r_ in
                 FStar_Syntax_DsEnv.push_namespace env1 uu___)
            open_namespaces dsenv1 in
        let dsenv3 =
          let uu___ = FStar_TypeChecker_Env.current_module env in
          FStar_Syntax_DsEnv.push_namespace dsenv2 uu___ in
        let dsenv4 =
          FStar_Compiler_List.fold_left
            (fun env1 ->
               fun uu___ ->
                 match uu___ with
                 | (m, n) ->
                     let uu___1 = FStar_Ident.id_of_text m in
                     let uu___2 = FStar_Ident.lid_of_path n r_ in
                     FStar_Syntax_DsEnv.push_module_abbrev env1 uu___1 uu___2)
            dsenv3 module_abbrevs in
        let env1 =
          {
            FStar_TypeChecker_Env.solver = (env.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range = (env.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (env.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma = (env.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (env.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (env.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (env.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (env.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab = (env.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (env.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (env.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (env.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (env.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (env.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (env.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (env.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq_strict =
              (env.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (env.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit = (env.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (env.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 = (env.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (env.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (env.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (env.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.intactics =
              (env.FStar_TypeChecker_Env.intactics);
            FStar_TypeChecker_Env.nocoerce =
              (env.FStar_TypeChecker_Env.nocoerce);
            FStar_TypeChecker_Env.tc_term =
              (env.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
              (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStar_TypeChecker_Env.universe_of =
              (env.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStar_TypeChecker_Env.teq_nosmt_force =
              (env.FStar_TypeChecker_Env.teq_nosmt_force);
            FStar_TypeChecker_Env.subtype_nosmt_force =
              (env.FStar_TypeChecker_Env.subtype_nosmt_force);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (env.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (env.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (env.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (env.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (env.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice = (env.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (env.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (env.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (env.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (env.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv = dsenv4;
            FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (env.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (env.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (env.FStar_TypeChecker_Env.enable_defer_to_tac);
            FStar_TypeChecker_Env.unif_allow_ref_guards =
              (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
            FStar_TypeChecker_Env.erase_erasable_args =
              (env.FStar_TypeChecker_Env.erase_erasable_args);
            FStar_TypeChecker_Env.core_check =
              (env.FStar_TypeChecker_Env.core_check)
          } in
        { tcenv = env1; local_refs = [] }