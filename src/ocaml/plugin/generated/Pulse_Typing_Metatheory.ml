open Prims
type ('g, 'c) comp_typing_u = (unit, unit, unit) Pulse_Typing.comp_typing
let (admit_st_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_comp -> (unit, unit) Pulse_Typing.st_comp_typing)
  =
  fun g ->
    fun st ->
      Pulse_Typing.STC (g, st, (Pulse_Typing_Env.fresh g), (), (), ())
let (admit_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st -> (unit, unit) comp_typing_u)
  =
  fun g ->
    fun c ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Typing.CT_ST (g, st, (admit_st_comp_typing g st))
      | Pulse_Syntax_Base.C_STAtomic (inames, st) ->
          Pulse_Typing.CT_STAtomic
            (g, inames, st, (), (admit_st_comp_typing g st))
      | Pulse_Syntax_Base.C_STGhost (inames, st) ->
          Pulse_Typing.CT_STGhost
            (g, inames, st, (), (admit_st_comp_typing g st))
let (st_typing_correctness :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (unit, unit) comp_typing_u)
  = fun g -> fun t -> fun c -> fun uu___ -> admit_comp_typing g c
let (add_frame_well_typed :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) comp_typing_u ->
        Pulse_Syntax_Base.term -> unit -> (unit, unit) comp_typing_u)
  =
  fun g ->
    fun c ->
      fun ct ->
        fun f -> fun ft -> admit_comp_typing g (Pulse_Typing.add_frame c f)
let (comp_typing_inversion :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) comp_typing_u -> (unit, unit) Pulse_Typing.st_comp_typing)
  =
  fun g ->
    fun c ->
      fun ct ->
        match ct with
        | Pulse_Typing.CT_ST (uu___, uu___1, st) -> st
        | Pulse_Typing.CT_STAtomic (uu___, uu___1, uu___2, uu___3, st) -> st
        | Pulse_Typing.CT_STGhost (uu___, uu___1, uu___2, uu___3, st) -> st
let (st_comp_typing_inversion_cofinite :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_comp ->
      (unit, unit) Pulse_Typing.st_comp_typing -> (unit * unit * unit))
  = fun g -> fun st -> fun ct -> ((), (), ())
let (st_comp_typing_inversion :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_comp ->
      (unit, unit) Pulse_Typing.st_comp_typing ->
        (unit, unit, Pulse_Syntax_Base.var, unit) FStar_Pervasives.dtuple4)
  =
  fun g ->
    fun st ->
      fun ct ->
        let uu___ = ct in
        match uu___ with
        | Pulse_Typing.STC (g1, st1, x, ty, pre, post) ->
            FStar_Pervasives.Mkdtuple4 ((), (), x, ())
let (tm_exists_inversion :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          unit -> Pulse_Syntax_Base.var -> (unit * unit))
  = fun g -> fun u -> fun ty -> fun p -> fun uu___ -> fun x -> ((), ())


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
let (comp_st_with_pre :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp_st)
  =
  fun c ->
    fun pre ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Syntax_Base.C_ST
            {
              Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
              Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
              Pulse_Syntax_Base.pre = pre;
              Pulse_Syntax_Base.post = (st.Pulse_Syntax_Base.post)
            }
      | Pulse_Syntax_Base.C_STGhost (i, st) ->
          Pulse_Syntax_Base.C_STGhost
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = pre;
                Pulse_Syntax_Base.post = (st.Pulse_Syntax_Base.post)
              })
      | Pulse_Syntax_Base.C_STAtomic (i, st) ->
          Pulse_Syntax_Base.C_STAtomic
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = pre;
                Pulse_Syntax_Base.post = (st.Pulse_Syntax_Base.post)
              })
type ('g, 'gu, 'guu) pairwise_disjoint = unit
let (st_typing_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Typing_Env.env -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g -> fun g' -> fun t -> fun c -> fun uu___ -> fun g1 -> Prims.magic ()
let (singleton_env :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Syntax_Base.var -> Pulse_Syntax_Base.typ -> Pulse_Typing_Env.env)
  =
  fun f ->
    fun x ->
      fun t ->
        Pulse_Typing_Env.push_binding (Pulse_Typing_Env.mk_env f) x
          Pulse_Syntax_Base.ppname_default t
let (nt :
  Pulse_Syntax_Base.var ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Naming.subst_elt Prims.list)
  = fun x -> fun t -> [Pulse_Syntax_Naming.NT (x, t)]
let (subst_env :
  Pulse_Typing_Env.env -> Pulse_Syntax_Naming.subst -> Pulse_Typing_Env.env)
  = fun en -> fun ss -> Prims.admit ()
let (st_typing_subst :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.typ ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.st_term ->
                Pulse_Syntax_Base.comp_st ->
                  (unit, unit, unit) Pulse_Typing.st_typing ->
                    (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun x ->
      fun t ->
        fun g' ->
          fun e ->
            fun e_typing ->
              fun e1 -> fun c1 -> fun e1_typing -> Prims.admit ()