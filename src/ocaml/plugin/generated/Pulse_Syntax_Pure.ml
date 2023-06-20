open Prims
let op_let_Question :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a -> 'b FStar_Pervasives_Native.option) ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun g ->
      match f with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x -> g x
let (u0 : Pulse_Syntax_Base.universe) =
  FStar_Reflection_V2_Builtins.pack_universe FStar_Reflection_V2_Data.Uv_Zero
let (u1 : Pulse_Syntax_Base.universe) =
  FStar_Reflection_V2_Builtins.pack_universe
    (FStar_Reflection_V2_Data.Uv_Succ u0)
let (u2 : Pulse_Syntax_Base.universe) =
  FStar_Reflection_V2_Builtins.pack_universe
    (FStar_Reflection_V2_Data.Uv_Succ u1)
let (u_zero : Pulse_Syntax_Base.universe) = u0
let (u_succ : Pulse_Syntax_Base.universe -> Pulse_Syntax_Base.universe) =
  fun u ->
    FStar_Reflection_V2_Builtins.pack_universe
      (FStar_Reflection_V2_Data.Uv_Succ u)
let (u_var : Prims.string -> Pulse_Syntax_Base.universe) =
  fun s ->
    FStar_Reflection_V2_Builtins.pack_universe
      (FStar_Reflection_V2_Data.Uv_Name
         (FStar_Reflection_V2_Builtins.pack_ident (s, FStar_Range.range_0)))
let (u_max :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.universe -> Pulse_Syntax_Base.universe)
  =
  fun u01 ->
    fun u11 ->
      FStar_Reflection_V2_Builtins.pack_universe
        (FStar_Reflection_V2_Data.Uv_Max [u01; u11])
let (u_unknown : Pulse_Syntax_Base.universe) =
  FStar_Reflection_V2_Builtins.pack_universe FStar_Reflection_V2_Data.Uv_Unk
let (tm_bvar : Pulse_Syntax_Base.bv -> Pulse_Syntax_Base.term) =
  fun bv ->
    Pulse_Syntax_Base.tm_fstar
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_BVar
            (FStar_Reflection_V2_Builtins.pack_bv
               (FStar_Reflection_Typing.make_bv_with_name
                  (bv.Pulse_Syntax_Base.bv_ppname).Pulse_Syntax_Base.name
                  bv.Pulse_Syntax_Base.bv_index))))
      (bv.Pulse_Syntax_Base.bv_ppname).Pulse_Syntax_Base.range
let (tm_var : Pulse_Syntax_Base.nm -> Pulse_Syntax_Base.term) =
  fun nm ->
    Pulse_Syntax_Base.tm_fstar
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_Var
            (FStar_Reflection_V2_Builtins.pack_namedv
               (FStar_Reflection_Typing.make_namedv_with_name
                  (nm.Pulse_Syntax_Base.nm_ppname).Pulse_Syntax_Base.name
                  nm.Pulse_Syntax_Base.nm_index))))
      (nm.Pulse_Syntax_Base.nm_ppname).Pulse_Syntax_Base.range
let (tm_fvar : Pulse_Syntax_Base.fv -> Pulse_Syntax_Base.term) =
  fun l ->
    Pulse_Syntax_Base.tm_fstar
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv l.Pulse_Syntax_Base.fv_name)))
      l.Pulse_Syntax_Base.fv_range
let (tm_uinst :
  Pulse_Syntax_Base.fv ->
    Pulse_Syntax_Base.universe Prims.list -> Pulse_Syntax_Base.term)
  =
  fun l ->
    fun us ->
      Pulse_Syntax_Base.tm_fstar
        (FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_UInst
              ((FStar_Reflection_V2_Builtins.pack_fv
                  l.Pulse_Syntax_Base.fv_name), us)))
        l.Pulse_Syntax_Base.fv_range
let (tm_constant : Pulse_Syntax_Base.constant -> Pulse_Syntax_Base.term) =
  fun c ->
    Pulse_Syntax_Base.tm_fstar
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_Const c)) FStar_Range.range_0
let (tm_refine :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun b ->
    fun t ->
      let rb =
        FStar_Reflection_Typing.mk_simple_binder
          (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name
          (Pulse_Elaborate_Pure.elab_term b.Pulse_Syntax_Base.binder_ty) in
      Pulse_Syntax_Base.tm_fstar
        (FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_Refine
              (rb, (Pulse_Elaborate_Pure.elab_term t)))) FStar_Range.range_0
let (tm_let :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun t ->
    fun e1 ->
      fun e2 ->
        let rb =
          FStar_Reflection_Typing.mk_simple_binder
            FStar_Reflection_Typing.pp_name_default
            (Pulse_Elaborate_Pure.elab_term t) in
        Pulse_Syntax_Base.tm_fstar
          (FStar_Reflection_V2_Builtins.pack_ln
             (FStar_Reflection_V2_Data.Tv_Let
                (false, [], rb, (Pulse_Elaborate_Pure.elab_term e1),
                  (Pulse_Elaborate_Pure.elab_term e2)))) FStar_Range.range_0
let (tm_pureapp :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun head ->
    fun q ->
      fun arg ->
        Pulse_Syntax_Base.tm_fstar
          (FStar_Reflection_V2_Derived.mk_app
             (Pulse_Elaborate_Pure.elab_term head)
             [((Pulse_Elaborate_Pure.elab_term arg),
                (Pulse_Elaborate_Pure.elab_qual q))]) FStar_Range.range_0
let (tm_arrow :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.term)
  =
  fun b ->
    fun q ->
      fun c ->
        Pulse_Syntax_Base.tm_fstar
          (Pulse_Reflection_Util.mk_arrow_with_name
             (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name
             ((Pulse_Elaborate_Pure.elab_term b.Pulse_Syntax_Base.binder_ty),
               (Pulse_Elaborate_Pure.elab_qual q))
             (Pulse_Elaborate_Pure.elab_comp c)) FStar_Range.range_0
let (tm_type : Pulse_Syntax_Base.universe -> Pulse_Syntax_Base.term) =
  fun u ->
    Pulse_Syntax_Base.tm_fstar
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_Type u)) FStar_Range.range_0
let (mk_bvar :
  Prims.string ->
    FStar_Range.range -> Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term)
  =
  fun s ->
    fun r ->
      fun i ->
        tm_bvar
          {
            Pulse_Syntax_Base.bv_index = i;
            Pulse_Syntax_Base.bv_ppname =
              (Pulse_Syntax_Base.mk_ppname
                 (FStar_Reflection_Typing.seal_pp_name s) r)
          }
let (null_var : Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term) =
  fun v ->
    tm_var
      {
        Pulse_Syntax_Base.nm_index = v;
        Pulse_Syntax_Base.nm_ppname = Pulse_Syntax_Base.ppname_default
      }
let (null_bvar : Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term) =
  fun i ->
    tm_bvar
      {
        Pulse_Syntax_Base.bv_index = i;
        Pulse_Syntax_Base.bv_ppname = Pulse_Syntax_Base.ppname_default
      }
let (term_of_nvar : Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.term) =
  fun x ->
    tm_var
      {
        Pulse_Syntax_Base.nm_index = (FStar_Pervasives_Native.snd x);
        Pulse_Syntax_Base.nm_ppname = (FStar_Pervasives_Native.fst x)
      }
let (term_of_no_name_var : Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term) =
  fun x -> term_of_nvar (Pulse_Syntax_Base.v_as_nv x)
let (is_var :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.nm FStar_Pervasives_Native.option)
  =
  fun t ->
    match t.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_FStar host_term ->
        (match FStar_Reflection_V2_Builtins.inspect_ln host_term with
         | FStar_Reflection_V2_Data.Tv_Var nv ->
             let nv_view = FStar_Reflection_V2_Builtins.inspect_namedv nv in
             FStar_Pervasives_Native.Some
               {
                 Pulse_Syntax_Base.nm_index =
                   (nv_view.FStar_Reflection_V2_Data.uniq);
                 Pulse_Syntax_Base.nm_ppname =
                   (Pulse_Syntax_Base.mk_ppname
                      nv_view.FStar_Reflection_V2_Data.ppname
                      t.Pulse_Syntax_Base.range1)
               }
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (is_fvar :
  Pulse_Syntax_Base.term ->
    (FStar_Reflection_Types.name * Pulse_Syntax_Base.universe Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match t.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_FStar host_term ->
        (match FStar_Reflection_V2_Builtins.inspect_ln host_term with
         | FStar_Reflection_V2_Data.Tv_FVar fv ->
             FStar_Pervasives_Native.Some
               ((FStar_Reflection_V2_Builtins.inspect_fv fv), [])
         | FStar_Reflection_V2_Data.Tv_UInst (fv, us) ->
             FStar_Pervasives_Native.Some
               ((FStar_Reflection_V2_Builtins.inspect_fv fv), us)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (is_pure_app :
  Pulse_Syntax_Base.term ->
    (Pulse_Syntax_Base.term * Pulse_Syntax_Base.qualifier
      FStar_Pervasives_Native.option * Pulse_Syntax_Base.term)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match t.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_FStar host_term ->
        (match FStar_Reflection_V2_Builtins.inspect_ln host_term with
         | FStar_Reflection_V2_Data.Tv_App (hd, (arg, q)) ->
             op_let_Question
               (match Pulse_Readback.readback_ty hd with
                | FStar_Pervasives_Native.Some hd1 ->
                    FStar_Pervasives_Native.Some hd1
                | uu___ -> FStar_Pervasives_Native.None)
               (fun hd1 ->
                  let q1 = Pulse_Readback.readback_qual q in
                  op_let_Question
                    (match Pulse_Readback.readback_ty arg with
                     | FStar_Pervasives_Native.Some arg1 ->
                         FStar_Pervasives_Native.Some arg1
                     | uu___ -> FStar_Pervasives_Native.None)
                    (fun arg1 -> FStar_Pervasives_Native.Some (hd1, q1, arg1)))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (leftmost_head :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match t.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_FStar host_term ->
        let uu___ = FStar_Reflection_V2_Derived.collect_app_ln host_term in
        (match uu___ with
         | (hd, uu___1) ->
             (match Pulse_Readback.readback_ty hd with
              | FStar_Pervasives_Native.Some t1 ->
                  FStar_Pervasives_Native.Some t1
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
    | uu___ -> FStar_Pervasives_Native.None
let (is_fvar_app :
  Pulse_Syntax_Base.term ->
    (FStar_Reflection_Types.name * Pulse_Syntax_Base.universe Prims.list *
      Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option *
      Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match is_fvar t with
    | FStar_Pervasives_Native.Some (l, us) ->
        FStar_Pervasives_Native.Some
          (l, us, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
    | FStar_Pervasives_Native.None ->
        (match is_pure_app t with
         | FStar_Pervasives_Native.Some (head, q, arg) ->
             (match is_fvar head with
              | FStar_Pervasives_Native.Some (l, us) ->
                  FStar_Pervasives_Native.Some
                    (l, us, q, (FStar_Pervasives_Native.Some arg))
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
         | uu___ -> FStar_Pervasives_Native.None)
let (is_arrow :
  Pulse_Syntax_Base.term ->
    (Pulse_Syntax_Base.binder * Pulse_Syntax_Base.qualifier
      FStar_Pervasives_Native.option * Pulse_Syntax_Base.comp)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match t.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_FStar host_term ->
        (match FStar_Reflection_V2_Builtins.inspect_ln host_term with
         | FStar_Reflection_V2_Data.Tv_Arrow (b, c) ->
             let uu___ = FStar_Reflection_V2_Builtins.inspect_binder b in
             (match uu___ with
              | { FStar_Reflection_V2_Data.sort2 = sort;
                  FStar_Reflection_V2_Data.qual = qual;
                  FStar_Reflection_V2_Data.attrs = uu___1;
                  FStar_Reflection_V2_Data.ppname2 = ppname;_} ->
                  (match qual with
                   | FStar_Reflection_V2_Data.Q_Meta uu___2 ->
                       FStar_Pervasives_Native.None
                   | uu___2 ->
                       let q = Pulse_Readback.readback_qual qual in
                       let c_view =
                         FStar_Reflection_V2_Builtins.inspect_comp c in
                       (match c_view with
                        | FStar_Reflection_V2_Data.C_Total c_t ->
                            op_let_Question (Pulse_Readback.readback_ty sort)
                              (fun binder_ty ->
                                 op_let_Question
                                   (match Pulse_Readback.readback_comp c_t
                                    with
                                    | FStar_Pervasives_Native.Some c1 ->
                                        FStar_Pervasives_Native.Some c1
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Pervasives_Native.None)
                                   (fun c1 ->
                                      FStar_Pervasives_Native.Some
                                        ({
                                           Pulse_Syntax_Base.binder_ty =
                                             binder_ty;
                                           Pulse_Syntax_Base.binder_ppname =
                                             (Pulse_Syntax_Base.mk_ppname
                                                ppname
                                                (FStar_Reflection_V2_Builtins.range_of_term
                                                   host_term))
                                         }, q, c1)))
                        | uu___3 -> FStar_Pervasives_Native.None)))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (is_eq2 :
  Pulse_Syntax_Base.term ->
    (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match is_pure_app t with
    | FStar_Pervasives_Native.Some (head, FStar_Pervasives_Native.None, a2)
        ->
        (match is_pure_app head with
         | FStar_Pervasives_Native.Some
             (head1, FStar_Pervasives_Native.None, a1) ->
             (match is_pure_app head1 with
              | FStar_Pervasives_Native.Some
                  (head2, FStar_Pervasives_Native.Some
                   (Pulse_Syntax_Base.Implicit), uu___)
                  ->
                  (match is_fvar head2 with
                   | FStar_Pervasives_Native.Some (l, uu___1) ->
                       if
                         (l = ["Pulse"; "Steel"; "Wrapper"; "eq2_prop"]) ||
                           (l = ["Prims"; "eq2"])
                       then FStar_Pervasives_Native.Some (a1, a2)
                       else FStar_Pervasives_Native.None
                   | uu___1 -> FStar_Pervasives_Native.None)
              | uu___ -> FStar_Pervasives_Native.None)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (unreveal :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match is_pure_app t with
    | FStar_Pervasives_Native.Some (head, FStar_Pervasives_Native.None, arg)
        ->
        (match is_pure_app head with
         | FStar_Pervasives_Native.Some
             (head1, FStar_Pervasives_Native.Some
              (Pulse_Syntax_Base.Implicit), uu___)
             ->
             (match is_fvar head1 with
              | FStar_Pervasives_Native.Some (l, []) ->
                  if l = ["FStar"; "Ghost"; "reveal"]
                  then FStar_Pervasives_Native.Some arg
                  else FStar_Pervasives_Native.None
              | uu___1 -> FStar_Pervasives_Native.None)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None