open Prims
type var = Prims.string
type binding = (var * Pulse2Rust_Rust_Syntax.typ * Prims.bool)
type env =
  {
  fns: (Prims.string * Pulse2Rust_Rust_Syntax.fn_signature) Prims.list ;
  statics: (Prims.string * Pulse2Rust_Rust_Syntax.typ) Prims.list ;
  gamma: binding Prims.list }
let (__proj__Mkenv__item__fns :
  env -> (Prims.string * Pulse2Rust_Rust_Syntax.fn_signature) Prims.list) =
  fun projectee -> match projectee with | { fns; statics; gamma;_} -> fns
let (__proj__Mkenv__item__statics :
  env -> (Prims.string * Pulse2Rust_Rust_Syntax.typ) Prims.list) =
  fun projectee -> match projectee with | { fns; statics; gamma;_} -> statics
let (__proj__Mkenv__item__gamma : env -> binding Prims.list) =
  fun projectee -> match projectee with | { fns; statics; gamma;_} -> gamma
let (tyvar_of : Prims.string -> Prims.string) =
  fun s ->
    let uu___ =
      FStar_Compiler_String.substring s Prims.int_one
        ((FStar_Compiler_String.length s) - Prims.int_one) in
    FStar_Compiler_String.uppercase uu___
let (varname : Prims.string -> Prims.string) =
  fun s -> FStar_Compiler_Util.replace_char s 39 95
let (is_internal_name : Prims.string -> Prims.bool) =
  fun s ->
    (((((s = "uu___") || (s = "_fret")) || (s = "_bind_c")) ||
        (s = "_while_c"))
       || (s = "_while_b"))
      || (s = "_if_br")
let fail : 'uuuuu . Prims.string -> 'uuuuu =
  fun s ->
    let uu___ =
      FStar_Compiler_Util.format1 "Pulse to Rust extraction failed: %s" s in
    FStar_Compiler_Effect.failwith uu___
let fail_nyi : 'uuuuu . Prims.string -> 'uuuuu =
  fun s ->
    let uu___ =
      FStar_Compiler_Util.format1
        "Pulse to Rust extraction failed: no support yet for %s" s in
    FStar_Compiler_Effect.failwith uu___
let (empty_env : unit -> env) =
  fun uu___ -> { fns = []; statics = []; gamma = [] }
let (lookup_global_fn :
  env ->
    Prims.string ->
      Pulse2Rust_Rust_Syntax.fn_signature FStar_Pervasives_Native.option)
  =
  fun g ->
    fun s ->
      let uu___ =
        FStar_Compiler_List.tryFind
          (fun uu___1 -> match uu___1 with | (f, uu___2) -> f = s) g.fns in
      FStar_Compiler_Util.map_option
        (fun uu___1 -> match uu___1 with | (uu___2, t) -> t) uu___
let (lookup_local :
  env ->
    Prims.string ->
      (Pulse2Rust_Rust_Syntax.typ * Prims.bool)
        FStar_Pervasives_Native.option)
  =
  fun g ->
    fun s ->
      let uu___ =
        FStar_Compiler_List.tryFind
          (fun uu___1 -> match uu___1 with | (x, uu___2, uu___3) -> x = s)
          g.gamma in
      FStar_Compiler_Util.map_option
        (fun uu___1 -> match uu___1 with | (uu___2, t, b) -> (t, b)) uu___
let (push_fn :
  env -> Prims.string -> Pulse2Rust_Rust_Syntax.fn_signature -> env) =
  fun g ->
    fun s ->
      fun t ->
        { fns = ((s, t) :: (g.fns)); statics = (g.statics); gamma = (g.gamma)
        }
let (push_static : env -> Prims.string -> Pulse2Rust_Rust_Syntax.typ -> env)
  =
  fun g ->
    fun s ->
      fun t ->
        { fns = (g.fns); statics = ((s, t) :: (g.statics)); gamma = (g.gamma)
        }
let (push_local :
  env -> Prims.string -> Pulse2Rust_Rust_Syntax.typ -> Prims.bool -> env) =
  fun g ->
    fun s ->
      fun t ->
        fun is_mut ->
          {
            fns = (g.fns);
            statics = (g.statics);
            gamma = ((s, t, is_mut) :: (g.gamma))
          }
let (type_of : env -> Pulse2Rust_Rust_Syntax.expr -> Prims.bool) =
  fun g ->
    fun e ->
      match e with
      | Pulse2Rust_Rust_Syntax.Expr_path (s::[]) ->
          let uu___ = lookup_local g s in
          (match uu___ with
           | FStar_Pervasives_Native.Some (_t, b) -> b
           | FStar_Pervasives_Native.None ->
               let uu___1 =
                 FStar_Compiler_Util.format1 "lookup in env for %s" s in
               fail uu___1)
      | uu___ -> false
let rec (uncurry_arrow :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu___, t2) ->
        let uu___1 = uncurry_arrow t2 in
        (match uu___1 with | (arg_ts, ret_t) -> ((t1 :: arg_ts), ret_t))
    | uu___ -> ([], t)
let rec (extract_mlty :
  env -> FStar_Extraction_ML_Syntax.mlty -> Pulse2Rust_Rust_Syntax.typ) =
  fun g ->
    fun t ->
      let mk_slice is_mut t1 =
        let uu___ =
          let uu___1 =
            FStar_Compiler_Effect.op_Bar_Greater t1 (extract_mlty g) in
          FStar_Compiler_Effect.op_Bar_Greater uu___1
            Pulse2Rust_Rust_Syntax.mk_slice_typ in
        FStar_Compiler_Effect.op_Bar_Greater uu___
          (Pulse2Rust_Rust_Syntax.mk_ref_typ is_mut) in
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var s ->
          let uu___ = tyvar_of s in
          Pulse2Rust_Rust_Syntax.mk_scalar_typ uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.UInt32.t" ->
          Pulse2Rust_Rust_Syntax.mk_scalar_typ "u32"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.Int32.t" ->
          Pulse2Rust_Rust_Syntax.mk_scalar_typ "i32"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.UInt64.t" ->
          Pulse2Rust_Rust_Syntax.mk_scalar_typ "u64"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          ((let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___ = "FStar.Int64.t") ||
             (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___ = "Prims.int"))
            ||
            (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___ = "Prims.nat")
          -> Pulse2Rust_Rust_Syntax.mk_scalar_typ "i64"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.SizeT.t" ->
          Pulse2Rust_Rust_Syntax.mk_scalar_typ "usize"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Prims.bool" -> Pulse2Rust_Rust_Syntax.mk_scalar_typ "bool"
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Pulse.Lib.Reference.ref" ->
          let is_mut = true in
          let uu___ =
            FStar_Compiler_Effect.op_Bar_Greater arg (extract_mlty g) in
          FStar_Compiler_Effect.op_Bar_Greater uu___
            (Pulse2Rust_Rust_Syntax.mk_ref_typ is_mut)
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Pulse.Lib.Box.box" ->
          let uu___ =
            FStar_Compiler_Effect.op_Bar_Greater arg (extract_mlty g) in
          FStar_Compiler_Effect.op_Bar_Greater uu___
            Pulse2Rust_Rust_Syntax.mk_box_typ
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Pulse.Lib.Array.Core.array" ->
          let is_mut = true in mk_slice is_mut arg
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu___::[], p) when
          let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___1 = "Pulse.Lib.Array.Core.larray" ->
          let is_mut = true in mk_slice is_mut arg
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Pulse.Lib.Vec.vec" ->
          let uu___ =
            FStar_Compiler_Effect.op_Bar_Greater arg (extract_mlty g) in
          FStar_Compiler_Effect.op_Bar_Greater uu___
            Pulse2Rust_Rust_Syntax.mk_vec_typ
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.Pervasives.Native.option" ->
          let uu___ =
            FStar_Compiler_Effect.op_Bar_Greater arg (extract_mlty g) in
          FStar_Compiler_Effect.op_Bar_Greater uu___
            Pulse2Rust_Rust_Syntax.mk_option_typ
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu___::[], p) when
          let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___1 = "Pulse.Lib.Mutex.mutex" ->
          let uu___1 =
            let uu___2 =
              let uu___3 = let uu___4 = extract_mlty g arg in [uu___4] in
              {
                Pulse2Rust_Rust_Syntax.typ_path_segment_name = "Mutex";
                Pulse2Rust_Rust_Syntax.typ_path_segment_generic_args = uu___3
              } in
            [uu___2] in
          Pulse2Rust_Rust_Syntax.Typ_path uu___1
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Pulse.Lib.GlobalState.global_state" ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = extract_mlty g arg in [uu___3] in
              {
                Pulse2Rust_Rust_Syntax.typ_path_segment_name = "OnceLock";
                Pulse2Rust_Rust_Syntax.typ_path_segment_generic_args = uu___2
              } in
            [uu___1] in
          Pulse2Rust_Rust_Syntax.Typ_path uu___
      | FStar_Extraction_ML_Syntax.MLTY_Erased ->
          Pulse2Rust_Rust_Syntax.Typ_unit
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, p) ->
          let uu___ = FStar_Compiler_List.map (extract_mlty g) args in
          Pulse2Rust_Rust_Syntax.mk_named_typ (FStar_Pervasives_Native.snd p)
            uu___
      | FStar_Extraction_ML_Syntax.MLTY_Top ->
          Pulse2Rust_Rust_Syntax.Typ_infer
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Extraction_ML_Syntax.mlty_to_string t in
            FStar_Compiler_Util.format1 "mlty %s" uu___2 in
          fail_nyi uu___1
let (extract_mltyopt :
  env ->
    FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option ->
      Pulse2Rust_Rust_Syntax.typ)
  =
  fun g ->
    fun t ->
      match t with
      | FStar_Pervasives_Native.None -> Pulse2Rust_Rust_Syntax.Typ_infer
      | FStar_Pervasives_Native.Some t1 -> extract_mlty g t1
let (extract_top_level_fn_arg :
  env ->
    Prims.string ->
      FStar_Extraction_ML_Syntax.mlty -> Pulse2Rust_Rust_Syntax.fn_arg)
  =
  fun g ->
    fun arg_name ->
      fun t ->
        let uu___ = FStar_Compiler_Effect.op_Bar_Greater t (extract_mlty g) in
        FStar_Compiler_Effect.op_Bar_Greater uu___
          (Pulse2Rust_Rust_Syntax.mk_scalar_fn_arg arg_name)
let (push_fn_arg :
  env -> Prims.string -> Pulse2Rust_Rust_Syntax.fn_arg -> env) =
  fun g ->
    fun arg_name ->
      fun arg ->
        match arg with
        | Pulse2Rust_Rust_Syntax.Fn_arg_pat
            { Pulse2Rust_Rust_Syntax.pat_typ_pat = uu___;
              Pulse2Rust_Rust_Syntax.pat_typ_typ = pat_typ_typ;_}
            -> let is_mut = false in push_local g arg_name pat_typ_typ false
let (extract_top_level_sig :
  env ->
    Prims.string ->
      FStar_Extraction_ML_Syntax.mlidents ->
        Prims.string Prims.list ->
          FStar_Extraction_ML_Syntax.mlty Prims.list ->
            FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option ->
              (Pulse2Rust_Rust_Syntax.fn_signature * env))
  =
  fun g ->
    fun fn_name ->
      fun tvars ->
        fun arg_names ->
          fun arg_ts ->
            fun ret_t ->
              let fn_args =
                let uu___ = FStar_Compiler_List.map varname arg_names in
                FStar_Compiler_List.map2 (extract_top_level_fn_arg g) uu___
                  arg_ts in
              let fn_ret_t = extract_mltyopt g ret_t in
              let uu___ =
                let uu___1 = FStar_Compiler_List.map tyvar_of tvars in
                Pulse2Rust_Rust_Syntax.mk_fn_signature fn_name uu___1 fn_args
                  fn_ret_t in
              let uu___1 =
                let uu___2 = FStar_Compiler_List.zip arg_names fn_args in
                FStar_Compiler_List.fold_left
                  (fun g1 ->
                     fun uu___3 ->
                       match uu___3 with
                       | (arg_name, arg) -> push_fn_arg g1 arg_name arg) g
                  uu___2 in
              (uu___, uu___1)
let (arg_ts_and_ret_t :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty
      Prims.list * FStar_Extraction_ML_Syntax.mlty))
  =
  fun t ->
    let uu___ = t in
    match uu___ with
    | (tvars, t1) ->
        (match t1 with
         | FStar_Extraction_ML_Syntax.MLTY_Fun
             (uu___1, FStar_Extraction_ML_Syntax.E_PURE, uu___2) ->
             let uu___3 = uncurry_arrow t1 in
             (match uu___3 with | (arg_ts, ret_t) -> (tvars, arg_ts, ret_t))
         | FStar_Extraction_ML_Syntax.MLTY_Fun
             (uu___1, FStar_Extraction_ML_Syntax.E_IMPURE, uu___2) ->
             let uu___3 = uncurry_arrow t1 in
             (match uu___3 with | (arg_ts, ret_t) -> (tvars, arg_ts, ret_t))
         | uu___1 ->
             let uu___2 =
               let uu___3 = FStar_Extraction_ML_Syntax.mlty_to_string t1 in
               FStar_Compiler_Util.format1 "top level arg_ts and ret_t %s"
                 uu___3 in
             fail_nyi uu___2)
let (is_binop :
  Prims.string -> Pulse2Rust_Rust_Syntax.binop FStar_Pervasives_Native.option)
  =
  fun s ->
    if
      ((s = "Prims.op_Addition") || (s = "FStar.UInt32.add")) ||
        (s = "FStar.SizeT.add")
    then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Add
    else
      if s = "Prims.op_Subtraction"
      then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Sub
      else
        if s = "Prims.op_disEquality"
        then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Ne
        else
          if s = "Prims.op_LessThanOrEqual"
          then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Le
          else
            if
              ((s = "Prims.op_LessThan") || (s = "FStar.UInt32.lt")) ||
                (s = "FStar.SizeT.lt")
            then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Lt
            else
              if s = "Prims.op_GreaterThanOrEqual"
              then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Ge
              else
                if
                  ((s = "Prims.op_GreaterThan") || (s = "FStar.UInt32.gt"))
                    || (s = "FStar.SizeT.gt")
                then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Gt
                else
                  if s = "Prims.op_Equality"
                  then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Eq
                  else FStar_Pervasives_Native.None
let (extract_mlconstant_to_lit :
  FStar_Extraction_ML_Syntax.mlconstant -> Pulse2Rust_Rust_Syntax.lit) =
  fun c ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Int (lit_int_val, swopt) ->
        let lit_int_signed =
          match swopt with
          | FStar_Pervasives_Native.Some (FStar_Const.Unsigned, uu___) ->
              FStar_Pervasives_Native.Some false
          | FStar_Pervasives_Native.Some (FStar_Const.Signed, uu___) ->
              FStar_Pervasives_Native.Some true
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
        let lit_int_width =
          match swopt with
          | FStar_Pervasives_Native.Some (uu___, FStar_Const.Int8) ->
              FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.I8
          | FStar_Pervasives_Native.Some (uu___, FStar_Const.Int16) ->
              FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.I16
          | FStar_Pervasives_Native.Some (uu___, FStar_Const.Int32) ->
              FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.I32
          | FStar_Pervasives_Native.Some (uu___, FStar_Const.Int64) ->
              FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.I64
          | FStar_Pervasives_Native.Some (uu___, FStar_Const.Sizet) ->
              FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.I64
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
        Pulse2Rust_Rust_Syntax.Lit_int
          {
            Pulse2Rust_Rust_Syntax.lit_int_val = lit_int_val;
            Pulse2Rust_Rust_Syntax.lit_int_signed = lit_int_signed;
            Pulse2Rust_Rust_Syntax.lit_int_width = lit_int_width
          }
    | FStar_Extraction_ML_Syntax.MLC_Bool b ->
        Pulse2Rust_Rust_Syntax.Lit_bool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        Pulse2Rust_Rust_Syntax.Lit_string s
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Extraction_ML_Syntax.mlconstant_to_string c in
          FStar_Compiler_Util.format1 "mlconstant_to_lit %s" uu___2 in
        fail_nyi uu___1
let rec (extract_mlpattern_to_pat :
  FStar_Extraction_ML_Syntax.mlpattern -> Pulse2Rust_Rust_Syntax.pat) =
  fun p ->
    match p with
    | FStar_Extraction_ML_Syntax.MLP_Wild -> Pulse2Rust_Rust_Syntax.Pat_wild
    | FStar_Extraction_ML_Syntax.MLP_Const c ->
        let uu___ = extract_mlconstant_to_lit c in
        Pulse2Rust_Rust_Syntax.Pat_lit uu___
    | FStar_Extraction_ML_Syntax.MLP_Var x ->
        let uu___ = varname x in Pulse2Rust_Rust_Syntax.mk_pat_ident uu___
    | FStar_Extraction_ML_Syntax.MLP_CTor (p1, ps) ->
        let uu___ = FStar_Compiler_List.map extract_mlpattern_to_pat ps in
        Pulse2Rust_Rust_Syntax.mk_pat_ts (FStar_Pervasives_Native.snd p1)
          uu___
    | FStar_Extraction_ML_Syntax.MLP_Record (p1, fs) ->
        let uu___ = FStar_Compiler_List.last p1 in
        let uu___1 =
          FStar_Compiler_List.map
            (fun uu___2 ->
               match uu___2 with
               | (f, p2) ->
                   let uu___3 = extract_mlpattern_to_pat p2 in (f, uu___3))
            fs in
        Pulse2Rust_Rust_Syntax.mk_pat_struct uu___ uu___1
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Extraction_ML_Syntax.mlpattern_to_string p in
          FStar_Compiler_Util.format1 "mlpattern_to_pat %s" uu___2 in
        fail_nyi uu___1
let rec (lb_init_and_def :
  env ->
    FStar_Extraction_ML_Syntax.mllb ->
      (Prims.bool * Pulse2Rust_Rust_Syntax.typ * Pulse2Rust_Rust_Syntax.expr))
  =
  fun g ->
    fun lb ->
      let is_mut =
        FStar_Compiler_List.contains FStar_Extraction_ML_Syntax.Mutable
          lb.FStar_Extraction_ML_Syntax.mllb_meta in
      if is_mut
      then
        match (((lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr),
                (lb.FStar_Extraction_ML_Syntax.mllb_tysc))
        with
        | (FStar_Extraction_ML_Syntax.MLE_App
           ({
              FStar_Extraction_ML_Syntax.expr =
                FStar_Extraction_ML_Syntax.MLE_Name pe;
              FStar_Extraction_ML_Syntax.mlty = uu___;
              FStar_Extraction_ML_Syntax.loc = uu___1;_},
            init::[]),
           FStar_Pervasives_Native.Some
           ([], FStar_Extraction_ML_Syntax.MLTY_Named (ty::[], pt))) when
            (let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath pe in
             uu___2 = "Pulse.Lib.Reference.alloc") &&
              (let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath pt in
               uu___2 = "Pulse.Lib.Reference.ref")
            ->
            let uu___2 = extract_mlty g ty in
            let uu___3 = extract_mlexpr g init in (is_mut, uu___2, uu___3)
        | (FStar_Extraction_ML_Syntax.MLE_App
           ({
              FStar_Extraction_ML_Syntax.expr =
                FStar_Extraction_ML_Syntax.MLE_Name pe;
              FStar_Extraction_ML_Syntax.mlty = uu___;
              FStar_Extraction_ML_Syntax.loc = uu___1;_},
            init::len::[]),
           FStar_Pervasives_Native.Some
           ([], FStar_Extraction_ML_Syntax.MLTY_Named (ty::[], pt))) when
            (let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath pe in
             uu___2 = "Pulse.Lib.Array.Core.alloc") &&
              (let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath pt in
               uu___2 = "Pulse.Lib.Array.Core.array")
            ->
            let init1 = extract_mlexpr g init in
            let len1 = extract_mlexpr g len in
            let is_mut1 = false in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_Compiler_Effect.op_Bar_Greater
                    lb.FStar_Extraction_ML_Syntax.mllb_tysc
                    FStar_Compiler_Util.must in
                FStar_Compiler_Effect.op_Bar_Greater uu___4
                  FStar_Pervasives_Native.snd in
              FStar_Compiler_Effect.op_Bar_Greater uu___3 (extract_mlty g) in
            (is_mut1, uu___2,
              (Pulse2Rust_Rust_Syntax.mk_reference_expr true
                 (Pulse2Rust_Rust_Syntax.mk_repeat init1 len1)))
        | uu___ ->
            let uu___1 =
              let uu___2 =
                FStar_Extraction_ML_Syntax.mlexpr_to_string
                  lb.FStar_Extraction_ML_Syntax.mllb_def in
              FStar_Compiler_Util.format1
                "unexpected initializer for mutable local: %s" uu___2 in
            fail uu___1
      else
        (let is_mut1 =
           match (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
           with
           | FStar_Extraction_ML_Syntax.MLE_App
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Name p;
                       FStar_Extraction_ML_Syntax.mlty = uu___1;
                       FStar_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3::[]);
                  FStar_Extraction_ML_Syntax.mlty = uu___4;
                  FStar_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6)
               ->
               (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu___7 = "Pulse.Lib.Vec.alloc") ||
                 (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu___7 = "Pulse.Lib.Box.alloc")
           | uu___1 -> false in
         let uu___1 =
           let uu___2 =
             let uu___3 =
               FStar_Compiler_Effect.op_Bar_Greater
                 lb.FStar_Extraction_ML_Syntax.mllb_tysc
                 FStar_Compiler_Util.must in
             FStar_Compiler_Effect.op_Bar_Greater uu___3
               FStar_Pervasives_Native.snd in
           FStar_Compiler_Effect.op_Bar_Greater uu___2 (extract_mlty g) in
         let uu___2 = extract_mlexpr g lb.FStar_Extraction_ML_Syntax.mllb_def in
         (is_mut1, uu___1, uu___2))
and (extract_mlexpr :
  env -> FStar_Extraction_ML_Syntax.mlexpr -> Pulse2Rust_Rust_Syntax.expr) =
  fun g ->
    fun e ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit) ->
          Pulse2Rust_Rust_Syntax.Expr_lit Pulse2Rust_Rust_Syntax.Lit_unit
      | FStar_Extraction_ML_Syntax.MLE_Const c ->
          let lit = extract_mlconstant_to_lit c in
          Pulse2Rust_Rust_Syntax.Expr_lit lit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           e1::[])
          when
          let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___2 = "FStar.SizeT.uint_to_t" -> extract_mlexpr g e1
      | FStar_Extraction_ML_Syntax.MLE_Var x ->
          let uu___ = varname x in
          Pulse2Rust_Rust_Syntax.mk_expr_path_singl uu___
      | FStar_Extraction_ML_Syntax.MLE_Name p ->
          Pulse2Rust_Rust_Syntax.mk_expr_path_singl
            (FStar_Pervasives_Native.snd p)
      | FStar_Extraction_ML_Syntax.MLE_Let uu___ ->
          let uu___1 =
            FStar_Compiler_Effect.op_Bar_Greater e
              (extract_mlexpr_to_stmts g) in
          FStar_Compiler_Effect.op_Bar_Greater uu___1
            Pulse2Rust_Rust_Syntax.mk_block_expr
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::uu___5::[])
          when
          (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Reference.op_Colon_Equals") ||
            (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___6 = "Pulse.Lib.Box.op_Colon_Equals")
          ->
          let e11 = extract_mlexpr g e1 in
          let e21 = extract_mlexpr g e2 in
          let b = type_of g e11 in
          if b
          then Pulse2Rust_Rust_Syntax.mk_assign e11 e21
          else Pulse2Rust_Rust_Syntax.mk_ref_assign e11 e21
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::uu___5::uu___6::[])
          when
          let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___7 = "Pulse.Lib.Reference.op_Bang" -> extract_mlexpr g e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::uu___5::uu___6::[])
          when
          let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___7 = "Pulse.Lib.Box.op_Bang" ->
          let e2 = extract_mlexpr g e1 in
          let b = type_of g e2 in
          if b then e2 else Pulse2Rust_Rust_Syntax.mk_ref_read e2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Box.box_to_ref" ->
          let e2 = extract_mlexpr g e1 in
          let is_mut = true in
          Pulse2Rust_Rust_Syntax.mk_reference_expr is_mut e2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Box.alloc" ->
          let e2 = extract_mlexpr g e1 in
          Pulse2Rust_Rust_Syntax.mk_call
            (Pulse2Rust_Rust_Syntax.mk_expr_path
               ["std"; "boxed"; "Box"; "new"]) [e2]
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::i::uu___5::uu___6::[])
          when
          (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___7 = "Pulse.Lib.Array.Core.op_Array_Access") ||
            (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___7 = "Pulse.Lib.Vec.op_Array_Access")
          ->
          let uu___7 = extract_mlexpr g e1 in
          let uu___8 = extract_mlexpr g i in
          Pulse2Rust_Rust_Syntax.mk_expr_index uu___7 uu___8
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::e3::uu___5::[])
          when
          (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Array.Core.op_Array_Assignment") ||
            (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___6 = "Pulse.Lib.Vec.op_Array_Assignment")
          ->
          let e11 = extract_mlexpr g e1 in
          let e21 = extract_mlexpr g e2 in
          let e31 = extract_mlexpr g e3 in
          Pulse2Rust_Rust_Syntax.mk_assign
            (Pulse2Rust_Rust_Syntax.mk_expr_index e11 e21) e31
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Vec.vec_to_array" ->
          let e2 = extract_mlexpr g e1 in
          let is_mut = true in
          Pulse2Rust_Rust_Syntax.mk_reference_expr is_mut e2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Vec.alloc" ->
          let e11 = extract_mlexpr g e1 in
          let e21 = extract_mlexpr g e2 in
          Pulse2Rust_Rust_Syntax.mk_call
            (Pulse2Rust_Rust_Syntax.mk_expr_path_singl
               Pulse2Rust_Rust_Syntax.vec_new_fn) [e11; e21]
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Array.Core.alloc" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_ML_Syntax.mlexpr_to_string e in
            FStar_Compiler_Util.format1 "mlexpr %s" uu___6 in
          fail_nyi uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::uu___5::[])
          when
          (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Vec.free") ||
            (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___6 = "Pulse.Lib.Box.free")
          ->
          let e2 = extract_mlexpr g e1 in
          Pulse2Rust_Rust_Syntax.mk_call
            (Pulse2Rust_Rust_Syntax.mk_expr_path_singl "drop") [e2]
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Array.Core.free" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_ML_Syntax.mlexpr_to_string e in
            FStar_Compiler_Util.format1 "mlexpr %s" uu___6 in
          fail_nyi uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Fun (uu___2, cond);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_}::{
                                                           FStar_Extraction_ML_Syntax.expr
                                                             =
                                                             FStar_Extraction_ML_Syntax.MLE_Fun
                                                             (uu___5, body);
                                                           FStar_Extraction_ML_Syntax.mlty
                                                             = uu___6;
                                                           FStar_Extraction_ML_Syntax.loc
                                                             = uu___7;_}::[])
          when
          let uu___8 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___8 = "Pulse.Lib.Core.while_" ->
          let expr_while_cond = extract_mlexpr g cond in
          let expr_while_body = extract_mlexpr_to_stmts g body in
          Pulse2Rust_Rust_Syntax.Expr_while
            {
              Pulse2Rust_Rust_Syntax.expr_while_cond = expr_while_cond;
              Pulse2Rust_Rust_Syntax.expr_while_body = expr_while_body
            }
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.GlobalState.get" ->
          let is_mut = false in
          let uu___5 =
            let uu___6 =
              let uu___7 = extract_mlexpr g e1 in
              Pulse2Rust_Rust_Syntax.mk_reference_expr is_mut uu___7 in
            [uu___6] in
          Pulse2Rust_Rust_Syntax.mk_call
            (Pulse2Rust_Rust_Syntax.Expr_path ["get"]) uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5)
          when
          let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___6 = "failwith" ->
          Pulse2Rust_Rust_Syntax.mk_call
            (Pulse2Rust_Rust_Syntax.mk_expr_path_singl
               Pulse2Rust_Rust_Syntax.panic_fn) []
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           e1::e2::[])
          when
          let uu___2 =
            let uu___3 =
              FStar_Compiler_Effect.op_Bar_Greater p
                FStar_Extraction_ML_Syntax.string_of_mlpath in
            FStar_Compiler_Effect.op_Bar_Greater uu___3 is_binop in
          FStar_Compiler_Effect.op_Bar_Greater uu___2
            FStar_Pervasives_Native.uu___is_Some
          ->
          let e11 = extract_mlexpr g e1 in
          let op =
            let uu___2 =
              let uu___3 =
                FStar_Compiler_Effect.op_Bar_Greater p
                  FStar_Extraction_ML_Syntax.string_of_mlpath in
              FStar_Compiler_Effect.op_Bar_Greater uu___3 is_binop in
            FStar_Compiler_Effect.op_Bar_Greater uu___2
              FStar_Compiler_Util.must in
          let e21 = extract_mlexpr g e2 in
          Pulse2Rust_Rust_Syntax.mk_binop e11 op e21
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 =
            let uu___6 =
              FStar_Compiler_Effect.op_Bar_Greater p
                FStar_Extraction_ML_Syntax.string_of_mlpath in
            FStar_Compiler_Effect.op_Bar_Greater uu___6 is_binop in
          FStar_Compiler_Effect.op_Bar_Greater uu___5
            FStar_Pervasives_Native.uu___is_Some
          ->
          let e11 = extract_mlexpr g e1 in
          let op =
            let uu___5 =
              let uu___6 =
                FStar_Compiler_Effect.op_Bar_Greater p
                  FStar_Extraction_ML_Syntax.string_of_mlpath in
              FStar_Compiler_Effect.op_Bar_Greater uu___6 is_binop in
            FStar_Compiler_Effect.op_Bar_Greater uu___5
              FStar_Compiler_Util.must in
          let e21 = extract_mlexpr g e2 in
          Pulse2Rust_Rust_Syntax.mk_binop e11 op e21
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           e1::e2::[])
          when
          let uu___2 =
            let uu___3 =
              FStar_Compiler_Effect.op_Bar_Greater p
                FStar_Extraction_ML_Syntax.string_of_mlpath in
            FStar_Compiler_Effect.op_Bar_Greater uu___3 is_binop in
          FStar_Compiler_Effect.op_Bar_Greater uu___2
            FStar_Pervasives_Native.uu___is_Some
          ->
          let e11 = extract_mlexpr g e1 in
          let op =
            let uu___2 =
              let uu___3 =
                FStar_Compiler_Effect.op_Bar_Greater p
                  FStar_Extraction_ML_Syntax.string_of_mlpath in
              FStar_Compiler_Effect.op_Bar_Greater uu___3 is_binop in
            FStar_Compiler_Effect.op_Bar_Greater uu___2
              FStar_Compiler_Util.must in
          let e21 = extract_mlexpr g e2 in
          Pulse2Rust_Rust_Syntax.mk_binop e11 op e21
      | FStar_Extraction_ML_Syntax.MLE_App (head, args) ->
          let head1 = extract_mlexpr g head in
          let args1 = FStar_Compiler_List.map (extract_mlexpr g) args in
          Pulse2Rust_Rust_Syntax.mk_call head1 args1
      | FStar_Extraction_ML_Syntax.MLE_CTor (p, args) ->
          let uu___ = FStar_Compiler_List.map (extract_mlexpr g) args in
          Pulse2Rust_Rust_Syntax.mk_call
            (Pulse2Rust_Rust_Syntax.mk_expr_path_singl
               (FStar_Pervasives_Native.snd p)) uu___
      | FStar_Extraction_ML_Syntax.MLE_TApp (head, uu___) ->
          extract_mlexpr g head
      | FStar_Extraction_ML_Syntax.MLE_If (cond, if_then, if_else_opt) ->
          let cond1 = extract_mlexpr g cond in
          let then_ = extract_mlexpr_to_stmts g if_then in
          let else_ =
            FStar_Compiler_Util.map_option (extract_mlexpr g) if_else_opt in
          let else_1 =
            match else_ with
            | FStar_Pervasives_Native.None -> else_
            | FStar_Pervasives_Native.Some (Pulse2Rust_Rust_Syntax.Expr_if
                uu___) -> else_
            | FStar_Pervasives_Native.Some (Pulse2Rust_Rust_Syntax.Expr_block
                uu___) -> else_
            | FStar_Pervasives_Native.Some else_2 ->
                FStar_Pervasives_Native.Some
                  (Pulse2Rust_Rust_Syntax.mk_block_expr
                     [Pulse2Rust_Rust_Syntax.Stmt_expr else_2]) in
          Pulse2Rust_Rust_Syntax.mk_if cond1 then_ else_1
      | FStar_Extraction_ML_Syntax.MLE_Match (e1, branches) ->
          let e2 = extract_mlexpr g e1 in
          let uu___ =
            FStar_Compiler_List.map (extract_mlbranch_to_arm g) branches in
          Pulse2Rust_Rust_Syntax.mk_match e2 uu___
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, uu___, uu___1) ->
          extract_mlexpr g e1
      | FStar_Extraction_ML_Syntax.MLE_Record (p, fields) ->
          let uu___ =
            FStar_Compiler_List.map
              (fun uu___1 ->
                 match uu___1 with
                 | (f, e1) -> let uu___2 = extract_mlexpr g e1 in (f, uu___2))
              fields in
          Pulse2Rust_Rust_Syntax.mk_expr_struct p uu___
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1, p) ->
          let uu___ = extract_mlexpr g e1 in
          Pulse2Rust_Rust_Syntax.mk_expr_field uu___
            (FStar_Pervasives_Native.snd p)
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Extraction_ML_Syntax.mlexpr_to_string e in
            FStar_Compiler_Util.format1 "mlexpr %s" uu___2 in
          fail_nyi uu___1
and (extract_mlexpr_to_stmts :
  env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      Pulse2Rust_Rust_Syntax.stmt Prims.list)
  =
  fun g ->
    fun e ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit) -> []
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((uu___,
            { FStar_Extraction_ML_Syntax.mllb_name = uu___1;
              FStar_Extraction_ML_Syntax.mllb_tysc = uu___2;
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu___3;
              FStar_Extraction_ML_Syntax.mllb_def =
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Const
                    (FStar_Extraction_ML_Syntax.MLC_Unit);
                  FStar_Extraction_ML_Syntax.mlty = uu___4;
                  FStar_Extraction_ML_Syntax.loc = uu___5;_};
              FStar_Extraction_ML_Syntax.mllb_meta = uu___6;
              FStar_Extraction_ML_Syntax.print_typ = uu___7;_}::[]),
           e1)
          -> extract_mlexpr_to_stmts g e1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((uu___,
            { FStar_Extraction_ML_Syntax.mllb_name = uu___1;
              FStar_Extraction_ML_Syntax.mllb_tysc = uu___2;
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu___3;
              FStar_Extraction_ML_Syntax.mllb_def =
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_App
                    ({
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_TApp
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Name p;
                            FStar_Extraction_ML_Syntax.mlty = uu___4;
                            FStar_Extraction_ML_Syntax.loc = uu___5;_},
                          uu___6);
                       FStar_Extraction_ML_Syntax.mlty = uu___7;
                       FStar_Extraction_ML_Syntax.loc = uu___8;_},
                     uu___9);
                  FStar_Extraction_ML_Syntax.mlty = uu___10;
                  FStar_Extraction_ML_Syntax.loc = uu___11;_};
              FStar_Extraction_ML_Syntax.mllb_meta = uu___12;
              FStar_Extraction_ML_Syntax.print_typ = uu___13;_}::[]),
           e1)
          when
          let uu___14 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___14 = "Pulse.Lib.GlobalState.put" ->
          extract_mlexpr_to_stmts g e1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((FStar_Extraction_ML_Syntax.NonRec, lb::[]), e1) ->
          let uu___ = lb_init_and_def g lb in
          (match uu___ with
           | (is_mut, ty, init) ->
               let s =
                 let uu___1 =
                   match lb.FStar_Extraction_ML_Syntax.mllb_tysc with
                   | FStar_Pervasives_Native.Some
                       (uu___2, FStar_Extraction_ML_Syntax.MLTY_Erased) ->
                       FStar_Pervasives_Native.None
                   | uu___2 ->
                       let uu___3 =
                         varname lb.FStar_Extraction_ML_Syntax.mllb_name in
                       FStar_Pervasives_Native.Some uu___3 in
                 Pulse2Rust_Rust_Syntax.mk_local_stmt uu___1 is_mut init in
               let uu___1 =
                 let uu___2 =
                   push_local g lb.FStar_Extraction_ML_Syntax.mllb_name ty
                     is_mut in
                 extract_mlexpr_to_stmts uu___2 e1 in
               s :: uu___1)
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5)
          when
          let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___6 = "failwith" ->
          [Pulse2Rust_Rust_Syntax.Stmt_expr
             (Pulse2Rust_Rust_Syntax.mk_call
                (Pulse2Rust_Rust_Syntax.mk_expr_path_singl
                   Pulse2Rust_Rust_Syntax.panic_fn) [])]
      | uu___ ->
          let uu___1 =
            let uu___2 = extract_mlexpr g e in
            Pulse2Rust_Rust_Syntax.Stmt_expr uu___2 in
          [uu___1]
and (extract_mlbranch_to_arm :
  env -> FStar_Extraction_ML_Syntax.mlbranch -> Pulse2Rust_Rust_Syntax.arm) =
  fun g ->
    fun uu___ ->
      match uu___ with
      | (pat, pat_guard, body) ->
          (match pat_guard with
           | FStar_Pervasives_Native.Some e ->
               let uu___1 =
                 let uu___2 = FStar_Extraction_ML_Syntax.mlexpr_to_string e in
                 FStar_Compiler_Util.format1
                   "mlbranch_to_arm with pat guard %s" uu___2 in
               fail_nyi uu___1
           | FStar_Pervasives_Native.None ->
               let pat1 = extract_mlpattern_to_pat pat in
               let arm_body = extract_mlexpr g body in
               Pulse2Rust_Rust_Syntax.mk_arm pat1 arm_body)
let (extract_top_level_lb :
  env ->
    FStar_Extraction_ML_Syntax.mlletbinding ->
      (Pulse2Rust_Rust_Syntax.item * env))
  =
  fun g ->
    fun lbs ->
      let uu___ = lbs in
      match uu___ with
      | (is_rec, lbs1) ->
          if is_rec = FStar_Extraction_ML_Syntax.Rec
          then fail_nyi "recursive let bindings"
          else
            (let uu___2 = lbs1 in
             match uu___2 with
             | lb::[] ->
                 (match (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                  with
                  | FStar_Extraction_ML_Syntax.MLE_Fun (bs, body) ->
                      let arg_names =
                        FStar_Compiler_List.map FStar_Pervasives_Native.fst
                          bs in
                      let uu___3 =
                        match lb.FStar_Extraction_ML_Syntax.mllb_tysc with
                        | FStar_Pervasives_Native.Some tsc ->
                            let uu___4 = arg_ts_and_ret_t tsc in
                            (match uu___4 with
                             | (tvars, arg_ts, ret_t) ->
                                 (tvars, arg_ts,
                                   (FStar_Pervasives_Native.Some ret_t)))
                        | FStar_Pervasives_Native.None ->
                            let uu___4 =
                              FStar_Compiler_List.map
                                FStar_Pervasives_Native.snd bs in
                            ([], uu___4, FStar_Pervasives_Native.None) in
                      (match uu___3 with
                       | (tvars, arg_ts, ret_t) ->
                           let uu___4 =
                             extract_top_level_sig g
                               lb.FStar_Extraction_ML_Syntax.mllb_name tvars
                               arg_names arg_ts ret_t in
                           (match uu___4 with
                            | (fn_sig, g_body) ->
                                let fn_body =
                                  extract_mlexpr_to_stmts g_body body in
                                let uu___5 =
                                  push_fn g
                                    lb.FStar_Extraction_ML_Syntax.mllb_name
                                    fn_sig in
                                ((Pulse2Rust_Rust_Syntax.Item_fn
                                    (Pulse2Rust_Rust_Syntax.mk_fn fn_sig
                                       fn_body)), uu___5)))
                  | uu___3 ->
                      (match lb.FStar_Extraction_ML_Syntax.mllb_tysc with
                       | FStar_Pervasives_Native.Some ([], ty) ->
                           let name = lb.FStar_Extraction_ML_Syntax.mllb_name in
                           let ty1 = extract_mlty g ty in
                           let e =
                             match (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                             with
                             | FStar_Extraction_ML_Syntax.MLE_App
                                 ({
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_TApp
                                      ({
                                         FStar_Extraction_ML_Syntax.expr =
                                           FStar_Extraction_ML_Syntax.MLE_Name
                                           p1;
                                         FStar_Extraction_ML_Syntax.mlty =
                                           uu___4;
                                         FStar_Extraction_ML_Syntax.loc =
                                           uu___5;_},
                                       uu___6);
                                    FStar_Extraction_ML_Syntax.mlty = uu___7;
                                    FStar_Extraction_ML_Syntax.loc = uu___8;_},
                                  uu___9::{
                                            FStar_Extraction_ML_Syntax.expr =
                                              FStar_Extraction_ML_Syntax.MLE_App
                                              ({
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   FStar_Extraction_ML_Syntax.MLE_TApp
                                                   ({
                                                      FStar_Extraction_ML_Syntax.expr
                                                        =
                                                        FStar_Extraction_ML_Syntax.MLE_Name
                                                        p2;
                                                      FStar_Extraction_ML_Syntax.mlty
                                                        = uu___10;
                                                      FStar_Extraction_ML_Syntax.loc
                                                        = uu___11;_},
                                                    uu___12);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = uu___13;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   = uu___14;_},
                                               uu___15);
                                            FStar_Extraction_ML_Syntax.mlty =
                                              uu___16;
                                            FStar_Extraction_ML_Syntax.loc =
                                              uu___17;_}::[])
                                 when
                                 (let uu___18 =
                                    FStar_Extraction_ML_Syntax.string_of_mlpath
                                      p1 in
                                  uu___18 = "GlobalStateTest.run_stt") &&
                                   (let uu___18 =
                                      FStar_Extraction_ML_Syntax.string_of_mlpath
                                        p2 in
                                    uu___18 = "Pulse.Lib.GlobalState.mk")
                                 ->
                                 Pulse2Rust_Rust_Syntax.Expr_call
                                   {
                                     Pulse2Rust_Rust_Syntax.expr_call_fn =
                                       (Pulse2Rust_Rust_Syntax.Expr_path
                                          ["OnceLock"; "new"]);
                                     Pulse2Rust_Rust_Syntax.expr_call_args =
                                       []
                                   }
                             | uu___4 ->
                                 extract_mlexpr g
                                   lb.FStar_Extraction_ML_Syntax.mllb_def in
                           let uu___4 = push_static g name ty1 in
                           ((Pulse2Rust_Rust_Syntax.mk_item_static name ty1 e),
                             uu___4)
                       | uu___4 ->
                           let uu___5 =
                             let uu___6 =
                               FStar_Extraction_ML_Syntax.mlexpr_to_string
                                 lb.FStar_Extraction_ML_Syntax.mllb_def in
                             FStar_Compiler_Util.format1
                               "top level lb def with either no tysc or generics %s"
                               uu___6 in
                           fail_nyi uu___5)))
let (extract_struct_defn :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      (Pulse2Rust_Rust_Syntax.item * env))
  =
  fun g ->
    fun d ->
      let uu___ = d.FStar_Extraction_ML_Syntax.tydecl_defn in
      match uu___ with
      | FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Record
          fts) ->
          let uu___1 =
            let uu___2 =
              FStar_Compiler_List.map tyvar_of
                d.FStar_Extraction_ML_Syntax.tydecl_parameters in
            let uu___3 =
              FStar_Compiler_List.map
                (fun uu___4 ->
                   match uu___4 with
                   | (f, t) -> let uu___5 = extract_mlty g t in (f, uu___5))
                fts in
            Pulse2Rust_Rust_Syntax.mk_item_struct
              d.FStar_Extraction_ML_Syntax.tydecl_name uu___2 uu___3 in
          (uu___1, g)
let (extract_type_abbrev :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      (Pulse2Rust_Rust_Syntax.item * env))
  =
  fun g ->
    fun d ->
      let uu___ = d.FStar_Extraction_ML_Syntax.tydecl_defn in
      match uu___ with
      | FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev
          t) ->
          let uu___1 =
            let uu___2 =
              FStar_Compiler_List.map tyvar_of
                d.FStar_Extraction_ML_Syntax.tydecl_parameters in
            let uu___3 = extract_mlty g t in
            Pulse2Rust_Rust_Syntax.mk_item_type
              d.FStar_Extraction_ML_Syntax.tydecl_name uu___2 uu___3 in
          (uu___1, g)
let (extract_enum :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      (Pulse2Rust_Rust_Syntax.item * env))
  =
  fun g ->
    fun d ->
      let uu___ = d.FStar_Extraction_ML_Syntax.tydecl_defn in
      match uu___ with
      | FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_DType
          cts) ->
          let uu___1 =
            let uu___2 =
              FStar_Compiler_List.map tyvar_of
                d.FStar_Extraction_ML_Syntax.tydecl_parameters in
            let uu___3 =
              FStar_Compiler_List.map
                (fun uu___4 ->
                   match uu___4 with
                   | (cname, dts) ->
                       let uu___5 =
                         FStar_Compiler_List.map
                           (fun uu___6 ->
                              match uu___6 with
                              | (uu___7, t) -> extract_mlty g t) dts in
                       (cname, uu___5)) cts in
            Pulse2Rust_Rust_Syntax.mk_item_enum
              d.FStar_Extraction_ML_Syntax.tydecl_name uu___2 uu___3 in
          (uu___1, g)
let (extract_mltydecl :
  env ->
    FStar_Extraction_ML_Syntax.mltydecl ->
      (Pulse2Rust_Rust_Syntax.item Prims.list * env))
  =
  fun g ->
    fun d ->
      FStar_Compiler_List.fold_left
        (fun uu___ ->
           fun d1 ->
             match uu___ with
             | (items, g1) ->
                 let f =
                   match d1.FStar_Extraction_ML_Syntax.tydecl_defn with
                   | FStar_Pervasives_Native.Some
                       (FStar_Extraction_ML_Syntax.MLTD_Abbrev uu___1) ->
                       extract_type_abbrev
                   | FStar_Pervasives_Native.Some
                       (FStar_Extraction_ML_Syntax.MLTD_Record uu___1) ->
                       extract_struct_defn
                   | FStar_Pervasives_Native.Some
                       (FStar_Extraction_ML_Syntax.MLTD_DType uu___1) ->
                       extract_enum
                   | uu___1 ->
                       let uu___2 =
                         let uu___3 =
                           FStar_Extraction_ML_Syntax.one_mltydecl_to_string
                             d1 in
                         FStar_Compiler_Util.format1 "mltydecl %s" uu___3 in
                       fail_nyi uu___2 in
                 let uu___1 = f g1 d1 in
                 (match uu___1 with
                  | (item, g2) ->
                      ((FStar_Compiler_List.op_At items [item]), g2)))
        ([], g) d
let (extract_one : Prims.string -> unit) =
  fun file ->
    let uu___ =
      let uu___1 = FStar_Compiler_Util.load_value_from_file file in
      match uu___1 with
      | FStar_Pervasives_Native.Some r -> r
      | FStar_Pervasives_Native.None ->
          FStar_Compiler_Effect.failwith "Could not load file" in
    match uu___ with
    | (gamma, decls) ->
        let uu___1 = uu___ in
        let uu___2 =
          FStar_Compiler_List.fold_left
            (fun uu___3 ->
               fun d ->
                 match uu___3 with
                 | (items, g) ->
                     ((let uu___5 =
                         FStar_Extraction_ML_Syntax.mlmodule1_to_string d in
                       FStar_Compiler_Util.print1 "Decl: %s\n" uu___5);
                      (match d with
                       | FStar_Extraction_ML_Syntax.MLM_Let lb ->
                           let uu___5 = extract_top_level_lb g lb in
                           (match uu___5 with
                            | (f, g1) ->
                                ((FStar_Compiler_List.op_At items [f]), g1))
                       | FStar_Extraction_ML_Syntax.MLM_Loc uu___5 ->
                           (items, g)
                       | FStar_Extraction_ML_Syntax.MLM_Ty d1 ->
                           let uu___5 = extract_mltydecl g d1 in
                           (match uu___5 with
                            | (d_items, g1) ->
                                ((FStar_Compiler_List.op_At items d_items),
                                  g1))
                       | uu___5 ->
                           let uu___6 =
                             let uu___7 =
                               FStar_Extraction_ML_Syntax.mlmodule1_to_string
                                 d in
                             FStar_Compiler_Util.format1 "top level decl %s"
                               uu___7 in
                           fail_nyi uu___6))) ([], (empty_env ())) decls in
        (match uu___2 with
         | (items, uu___3) ->
             let f = Pulse2Rust_Rust_Syntax.mk_file "a.rs" items in
             let s = RustBindings.file_to_rust f in
             FStar_Compiler_Util.print_string (Prims.strcat s "\n"))
let (extract : Prims.string Prims.list -> unit) =
  fun files -> FStar_Compiler_List.iter extract_one files