open Prims
let opt_bind :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a -> 'b FStar_Pervasives_Native.option) ->
        'b FStar_Pervasives_Native.option
  =
  fun m ->
    fun k ->
      match m with
      | FStar_Pervasives_Native.Some x -> k x
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (char_of_typechar :
  FStarC_Extraction_ML_Syntax.mlty ->
    FStarC_BaseTypes.char FStar_Pervasives_Native.option)
  =
  fun t ->
    match t with
    | FStarC_Extraction_ML_Syntax.MLTY_Named ([], p) ->
        let p1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
        if p1 = "Steel.C.Typestring.cdot"
        then FStar_Pervasives_Native.Some 46
        else
          if FStarC_Compiler_Util.starts_with p1 "Steel.C.Typestring.c"
          then
            (let uu___1 =
               FStarC_Compiler_String.get p1
                 (FStar_String.strlen "Steel.C.Typestring.c") in
             FStar_Pervasives_Native.Some uu___1)
          else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let (string_of_typestring :
  FStarC_Extraction_ML_Syntax.mlty ->
    Prims.string FStar_Pervasives_Native.option)
  =
  fun t ->
    let rec go t1 =
      match t1 with
      | FStarC_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Steel.C.Typestring.string_nil" ->
          FStar_Pervasives_Native.Some []
      | FStarC_Extraction_ML_Syntax.MLTY_Named (c::t2::[], p) when
          let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Steel.C.Typestring.string_cons" ->
          let uu___ = char_of_typechar c in
          opt_bind uu___
            (fun c' ->
               let uu___1 = go t2 in
               opt_bind uu___1
                 (fun s' ->
                    let uu___2 =
                      let uu___3 =
                        FStarC_Compiler_String.make Prims.int_one c' in
                      uu___3 :: s' in
                    FStar_Pervasives_Native.Some uu___2))
      | uu___ -> FStar_Pervasives_Native.None in
    let uu___ = go t in
    opt_bind uu___
      (fun ss -> FStar_Pervasives_Native.Some (FStar_String.concat "" ss))
let (lident_of_string :
  Prims.string -> FStarC_Extraction_Krml.lident FStar_Pervasives_Native.option)
  =
  fun s ->
    let path = FStar_String.split [46] s in
    let rec go p =
      match p with
      | [] -> FStar_Pervasives_Native.None
      | s1::[] -> FStar_Pervasives_Native.Some ([], s1)
      | s1::p1 ->
          let uu___ = go p1 in
          opt_bind uu___
            (fun uu___1 ->
               match uu___1 with
               | (names, name) ->
                   FStar_Pervasives_Native.Some ((s1 :: names), name)) in
    go path
let (lident_of_typestring :
  FStarC_Extraction_ML_Syntax.mlty ->
    FStarC_Extraction_Krml.lident FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = string_of_typestring t in opt_bind uu___ lident_of_string
let (int_of_typenat :
  FStarC_Extraction_ML_Syntax.mlty -> Prims.int FStar_Pervasives_Native.option)
  =
  fun t ->
    let rec go t1 =
      match t1 with
      | FStarC_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Steel.C.Typenat.z" ->
          FStar_Pervasives_Native.Some Prims.int_zero
      | FStarC_Extraction_ML_Syntax.MLTY_Named (t2::[], p) when
          let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Steel.C.Typenat.s" ->
          let uu___ = go t2 in
          opt_bind uu___
            (fun n -> FStar_Pervasives_Native.Some (n + Prims.int_one))
      | uu___ -> FStar_Pervasives_Native.None in
    go t
let (my_types_without_decay : unit -> unit) =
  fun uu___ ->
    FStarC_Extraction_Krml.register_pre_translate_type_without_decay
      (fun env ->
         fun t ->
           match t with
           | FStarC_Extraction_ML_Syntax.MLTY_Named
               (tag::uu___1::uu___2::uu___3::[], p) when
               (let uu___4 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                FStarC_Compiler_Util.starts_with uu___4
                  "Steel.ST.C.Types.Struct.struct_t0")
                 ||
                 (let uu___4 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                  FStarC_Compiler_Util.starts_with uu___4
                    "Steel.ST.C.Types.Union.union_t0")
               ->
               let uu___4 =
                 let uu___5 = lident_of_typestring tag in
                 FStarC_Compiler_Util.must uu___5 in
               FStarC_Extraction_Krml.TQualified uu___4
           | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
               let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___1 = "Steel.ST.C.Types.Array.array_ptr_gen" ->
               let uu___1 =
                 FStarC_Extraction_Krml.translate_type_without_decay env arg in
               FStarC_Extraction_Krml.TBuf uu___1
           | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
               let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___1 = "Steel.ST.C.Types.Base.ptr_gen" ->
               let uu___1 =
                 FStarC_Extraction_Krml.translate_type_without_decay env arg in
               FStarC_Extraction_Krml.TBuf uu___1
           | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
               let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___1 = "Steel.ST.C.Types.Scalar.scalar_t" ->
               FStarC_Extraction_Krml.translate_type_without_decay env arg
           | FStarC_Extraction_ML_Syntax.MLTY_Named ([], p) when
               (let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                uu___1 = "Steel.ST.C.Types.Base.void_ptr") ||
                 (let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                  uu___1 = "Steel.ST.C.Types.Array.array_void_ptr")
               ->
               ((let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                 FStarC_Compiler_Util.print1 "Converting %s to TAny" uu___2);
                FStarC_Extraction_Krml.TAny)
           | FStarC_Extraction_ML_Syntax.MLTY_Named (t1::n::s::[], p) when
               let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___1 = "Steel.ST.C.Types.Array.base_array_t" ->
               let uu___1 =
                 let uu___2 =
                   FStarC_Extraction_Krml.translate_type_without_decay env t1 in
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = int_of_typenat n in
                       FStarC_Compiler_Util.must uu___6 in
                     FStarC_Compiler_Util.string_of_int uu___5 in
                   (FStarC_Extraction_Krml.UInt32, uu___4) in
                 (uu___2, uu___3) in
               FStarC_Extraction_Krml.TArray uu___1
           | uu___1 ->
               FStarC_Compiler_Effect.raise
                 FStarC_Extraction_Krml.NotSupportedByKrmlExtension)
let (my_types : unit -> unit) =
  fun uu___ ->
    FStarC_Extraction_Krml.register_pre_translate_type
      (fun env ->
         fun t ->
           match t with
           | FStarC_Extraction_ML_Syntax.MLTY_Named
               (t1::uu___1::uu___2::[], p) when
               let uu___3 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___3 = "Steel.ST.C.Types.Array.base_array_t" ->
               let uu___3 =
                 FStarC_Extraction_Krml.translate_type_without_decay env t1 in
               FStarC_Extraction_Krml.TBuf uu___3
           | uu___1 ->
               FStarC_Compiler_Effect.raise
                 FStarC_Extraction_Krml.NotSupportedByKrmlExtension)
let (my_exprs : unit -> unit) =
  fun uu___ ->
    FStarC_Extraction_Krml.register_pre_translate_expr
      (fun env ->
         fun e ->
           match e.FStarC_Extraction_ML_Syntax.expr with
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::[])
               when
               (let uu___7 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                uu___7 = "Steel.ST.C.Types.Base.alloc") || false
               ->
               FStarC_Extraction_Krml.EBufCreateNoInit
                 (FStarC_Extraction_Krml.ManuallyManaged,
                   (FStarC_Extraction_Krml.EConstant
                      (FStarC_Extraction_Krml.UInt32, "1")))
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::sz::[])
               when
               (let uu___7 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                uu___7 = "Steel.ST.C.Types.Array.array_ptr_alloc") || false
               ->
               let uu___7 =
                 let uu___8 = FStarC_Extraction_Krml.translate_expr env sz in
                 (FStarC_Extraction_Krml.ManuallyManaged, uu___8) in
               FStarC_Extraction_Krml.EBufCreateNoInit uu___7
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::uu___7::e2::uu___8::[])
               when
               (let uu___9 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                uu___9 = "Steel.ST.C.Types.Array.array_ref_free") || false
               ->
               let uu___9 = FStarC_Extraction_Krml.translate_expr env e2 in
               FStarC_Extraction_Krml.EBufFree uu___9
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::uu___7::e1::[])
               when
               let uu___8 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___8 = "Steel.ST.C.Types.Base.free" ->
               let uu___8 = FStarC_Extraction_Krml.translate_expr env e1 in
               FStarC_Extraction_Krml.EBufFree uu___8
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     t::[]);
                  FStarC_Extraction_ML_Syntax.mlty = uu___3;
                  FStarC_Extraction_ML_Syntax.loc = uu___4;_},
                uu___5::uu___6::uu___7::e1::uu___8::[])
               when
               let uu___9 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___9 = "Steel.ST.C.Types.Array.array_ptr_is_null" ->
               let uu___9 = FStarC_Extraction_Krml.translate_type env t in
               let uu___10 = FStarC_Extraction_Krml.translate_expr env e1 in
               FStarC_Extraction_Krml.generate_is_null uu___9 uu___10
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     t::[]);
                  FStarC_Extraction_ML_Syntax.mlty = uu___3;
                  FStarC_Extraction_ML_Syntax.loc = uu___4;_},
                uu___5::uu___6::uu___7::e1::[])
               when
               let uu___8 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___8 = "Steel.ST.C.Types.Base.is_null" ->
               let uu___8 = FStarC_Extraction_Krml.translate_type env t in
               let uu___9 = FStarC_Extraction_Krml.translate_expr env e1 in
               FStarC_Extraction_Krml.generate_is_null uu___8 uu___9
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     t::[]);
                  FStarC_Extraction_ML_Syntax.mlty = uu___3;
                  FStarC_Extraction_ML_Syntax.loc = uu___4;_},
                uu___5)
               when
               (let uu___6 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                uu___6 = "Steel.ST.C.Types.Base.null_gen") ||
                 (let uu___6 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                  uu___6 = "Steel.ST.C.Types.Array.null_array_ptr")
               ->
               let uu___6 = FStarC_Extraction_Krml.translate_type env t in
               FStarC_Extraction_Krml.EBufNull uu___6
           | FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___1;
                  FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                t::[])
               when
               let uu___3 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___3 = "Steel.ST.C.Types.Base.null_gen" ->
               let uu___3 = FStarC_Extraction_Krml.translate_type env t in
               FStarC_Extraction_Krml.EBufNull uu___3
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                {
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Const
                    (FStarC_Extraction_ML_Syntax.MLC_String struct_name);
                  FStarC_Extraction_ML_Syntax.mlty = uu___6;
                  FStarC_Extraction_ML_Syntax.loc = uu___7;_}::uu___8::uu___9::r::
                {
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Const
                    (FStarC_Extraction_ML_Syntax.MLC_String field_name);
                  FStarC_Extraction_ML_Syntax.mlty = uu___10;
                  FStarC_Extraction_ML_Syntax.loc = uu___11;_}::uu___12::[])
               when
               ((let uu___13 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                 uu___13 = "Steel.ST.C.Types.Struct.struct_field0") ||
                  (let uu___13 =
                     FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                   uu___13 = "Steel.ST.C.Types.Union.union_field0"))
                 ||
                 (let uu___13 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                  uu___13 = "Steel.ST.C.Types.Union.union_switch_field0")
               ->
               let uu___13 =
                 let uu___14 =
                   let uu___15 =
                     let uu___16 =
                       let uu___17 = lident_of_string struct_name in
                       FStarC_Compiler_Util.must uu___17 in
                     FStarC_Extraction_Krml.TQualified uu___16 in
                   let uu___16 =
                     let uu___17 =
                       let uu___18 =
                         FStarC_Extraction_Krml.translate_expr env r in
                       (uu___18,
                         (FStarC_Extraction_Krml.EQualified
                            (["C"], "_zero_for_deref"))) in
                     FStarC_Extraction_Krml.EBufRead uu___17 in
                   (uu___15, uu___16, field_name) in
                 FStarC_Extraction_Krml.EField uu___14 in
               FStarC_Extraction_Krml.EAddrOf uu___13
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     t::uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::uu___7::r::{
                                     FStarC_Extraction_ML_Syntax.expr =
                                       FStarC_Extraction_ML_Syntax.MLE_Const
                                       (FStarC_Extraction_ML_Syntax.MLC_String
                                       field_name);
                                     FStarC_Extraction_ML_Syntax.mlty = uu___8;
                                     FStarC_Extraction_ML_Syntax.loc = uu___9;_}::uu___10::[])
               when
               let uu___11 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___11 = "Steel.ST.C.Types.UserStruct.struct_field0" ->
               let uu___11 =
                 let uu___12 =
                   let uu___13 = FStarC_Extraction_Krml.translate_type env t in
                   let uu___14 =
                     let uu___15 =
                       let uu___16 =
                         FStarC_Extraction_Krml.translate_expr env r in
                       (uu___16,
                         (FStarC_Extraction_Krml.EQualified
                            (["C"], "_zero_for_deref"))) in
                     FStarC_Extraction_Krml.EBufRead uu___15 in
                   (uu___13, uu___14, field_name) in
                 FStarC_Extraction_Krml.EField uu___12 in
               FStarC_Extraction_Krml.EAddrOf uu___11
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::uu___7::r::[])
               when
               let uu___8 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___8 = "Steel.ST.C.Types.Scalar.read0" ->
               let uu___8 =
                 let uu___9 = FStarC_Extraction_Krml.translate_expr env r in
                 (uu___9,
                   (FStarC_Extraction_Krml.EQualified
                      (["C"], "_zero_for_deref"))) in
               FStarC_Extraction_Krml.EBufRead uu___8
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::r::x::[])
               when
               let uu___7 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___7 = "Steel.ST.C.Types.Scalar.write" ->
               let uu___7 =
                 let uu___8 =
                   let uu___9 =
                     let uu___10 = FStarC_Extraction_Krml.translate_expr env r in
                     (uu___10,
                       (FStarC_Extraction_Krml.EQualified
                          (["C"], "_zero_for_deref"))) in
                   FStarC_Extraction_Krml.EBufRead uu___9 in
                 let uu___9 = FStarC_Extraction_Krml.translate_expr env x in
                 (uu___8, uu___9) in
               FStarC_Extraction_Krml.EAssign uu___7
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::uu___7::uu___8::uu___9::src::dst::[])
               when
               let uu___10 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___10 = "Steel.ST.C.Types.Base.copy" ->
               let uu___10 =
                 let uu___11 =
                   let uu___12 =
                     let uu___13 =
                       FStarC_Extraction_Krml.translate_expr env dst in
                     (uu___13,
                       (FStarC_Extraction_Krml.EQualified
                          (["C"], "_zero_for_deref"))) in
                   FStarC_Extraction_Krml.EBufRead uu___12 in
                 let uu___12 =
                   let uu___13 =
                     let uu___14 =
                       FStarC_Extraction_Krml.translate_expr env src in
                     (uu___14,
                       (FStarC_Extraction_Krml.EQualified
                          (["C"], "_zero_for_deref"))) in
                   FStarC_Extraction_Krml.EBufRead uu___13 in
                 (uu___11, uu___12) in
               FStarC_Extraction_Krml.EAssign uu___10
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::uu___7::uu___8::x::[])
               when
               let uu___9 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___9 = "Steel.ST.C.Types.Base.void_ptr_of_ptr" ->
               let uu___9 =
                 let uu___10 = FStarC_Extraction_Krml.translate_expr env x in
                 (uu___10, FStarC_Extraction_Krml.TAny) in
               FStarC_Extraction_Krml.ECast uu___9
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     t::[]);
                  FStarC_Extraction_ML_Syntax.mlty = uu___3;
                  FStarC_Extraction_ML_Syntax.loc = uu___4;_},
                uu___5::uu___6::uu___7::x::[])
               when
               let uu___8 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___8 = "Steel.ST.C.Types.Base.ptr_of_void_ptr" ->
               let uu___8 =
                 let uu___9 = FStarC_Extraction_Krml.translate_expr env x in
                 let uu___10 =
                   let uu___11 = FStarC_Extraction_Krml.translate_type env t in
                   FStarC_Extraction_Krml.TBuf uu___11 in
                 (uu___9, uu___10) in
               FStarC_Extraction_Krml.ECast uu___8
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::uu___7::uu___8::uu___9::r::[])
               when
               let uu___10 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___10 = "Steel.ST.C.Types.Array.array_ref_of_base" ->
               let uu___10 =
                 let uu___11 = FStarC_Extraction_Krml.translate_expr env r in
                 (uu___11,
                   (FStarC_Extraction_Krml.EQualified
                      (["C"], "_zero_for_deref"))) in
               FStarC_Extraction_Krml.EBufRead uu___10
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::uu___7::a::uu___8::i::[])
               when
               (let uu___9 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                uu___9 = "Steel.ST.C.Types.Array.array_ref_cell") ||
                 (let uu___9 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                  uu___9 = "Steel.ST.C.Types.Array.array_ref_split")
               ->
               let uu___9 =
                 let uu___10 = FStarC_Extraction_Krml.translate_expr env a in
                 let uu___11 = FStarC_Extraction_Krml.translate_expr env i in
                 (uu___10, uu___11) in
               FStarC_Extraction_Krml.EBufSub uu___9
           | FStarC_Extraction_ML_Syntax.MLE_App
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStarC_Extraction_ML_Syntax.expr =
                         FStarC_Extraction_ML_Syntax.MLE_Name p;
                       FStarC_Extraction_ML_Syntax.mlty = uu___1;
                       FStarC_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3);
                  FStarC_Extraction_ML_Syntax.mlty = uu___4;
                  FStarC_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6::uu___7::uu___8::uu___9::e1::uu___10::e2::e3::uu___11::e4::e5::[])
               when
               let uu___12 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___12 = "Steel.ST.C.Types.Array.array_blit_ptr" ->
               let uu___12 =
                 let uu___13 = FStarC_Extraction_Krml.translate_expr env e1 in
                 let uu___14 = FStarC_Extraction_Krml.translate_expr env e2 in
                 let uu___15 = FStarC_Extraction_Krml.translate_expr env e3 in
                 let uu___16 = FStarC_Extraction_Krml.translate_expr env e4 in
                 let uu___17 = FStarC_Extraction_Krml.translate_expr env e5 in
                 (uu___13, uu___14, uu___15, uu___16, uu___17) in
               FStarC_Extraction_Krml.EBufBlit uu___12
           | uu___1 ->
               FStarC_Compiler_Effect.raise
                 FStarC_Extraction_Krml.NotSupportedByKrmlExtension)
let (parse_steel_c_fields :
  FStarC_Extraction_Krml.env ->
    FStarC_Extraction_ML_Syntax.mlty ->
      (Prims.string * FStarC_Extraction_Krml.typ) Prims.list
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun fields ->
      let rec go fields1 =
        match fields1 with
        | FStarC_Extraction_ML_Syntax.MLTY_Named ([], p) when
            let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
            uu___ = "Steel.ST.C.Types.Fields.field_t_nil" ->
            FStar_Pervasives_Native.Some []
        | FStarC_Extraction_ML_Syntax.MLTY_Named (field::t::fields2::[], p)
            when
            let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
            uu___ = "Steel.ST.C.Types.Fields.field_t_cons" ->
            let uu___ = string_of_typestring field in
            opt_bind uu___
              (fun field1 ->
                 if field1 = ""
                 then go fields2
                 else
                   (let uu___2 = go fields2 in
                    opt_bind uu___2
                      (fun fields3 ->
                         FStar_Pervasives_Native.Some ((field1, t) ::
                           fields3))))
        | uu___ -> FStar_Pervasives_Native.None in
      let uu___ = go fields in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          ((let uu___2 =
              FStarC_Extraction_ML_Code.string_of_mlty ([], "") fields in
            FStarC_Compiler_Util.print1 "Failed to parse fields from %s.\n"
              uu___2);
           FStar_Pervasives_Native.None)
      | FStar_Pervasives_Native.Some fields1 ->
          (FStarC_Compiler_Util.print_endline "Got fields:";
           FStarC_Compiler_List.fold_left
             (fun uu___3 ->
                fun uu___4 ->
                  match uu___4 with
                  | (field, ty) ->
                      let uu___5 =
                        FStarC_Extraction_ML_Code.string_of_mlty ([], "") ty in
                      FStarC_Compiler_Util.print2 "  %s : %s\n" field uu___5)
             () fields1;
           (let uu___3 =
              FStarC_Compiler_List.map
                (fun uu___4 ->
                   match uu___4 with
                   | (field, ty) ->
                       ((let uu___6 =
                           FStarC_Extraction_ML_Code.string_of_mlty ([], "")
                             ty in
                         FStarC_Compiler_Util.print1 "Translating %s.\n"
                           uu___6);
                        (let uu___6 =
                           FStarC_Extraction_Krml.translate_type_without_decay
                             env ty in
                         (field, uu___6)))) fields1 in
            FStar_Pervasives_Native.Some uu___3))
let (define_struct_gen :
  FStarC_Extraction_Krml.env ->
    (Prims.string Prims.list * Prims.string) ->
      Prims.string Prims.list ->
        FStarC_Extraction_ML_Syntax.mlty ->
          FStarC_Extraction_Krml.decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun p ->
      fun args ->
        fun fields ->
          let env1 =
            FStarC_Compiler_List.fold_left
              (fun env2 ->
                 fun name -> FStarC_Extraction_Krml.extend_t env2 name) env
              args in
          let fields1 =
            let uu___ = parse_steel_c_fields env1 fields in
            FStarC_Compiler_Util.must uu___ in
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_Compiler_List.map
                  (fun uu___3 ->
                     match uu___3 with | (field, ty) -> (field, (ty, true)))
                  fields1 in
              (p, [], (FStarC_Compiler_List.length args), uu___2) in
            FStarC_Extraction_Krml.DTypeFlat uu___1 in
          FStar_Pervasives_Native.Some uu___
let (define_struct :
  FStarC_Extraction_Krml.env ->
    FStarC_Extraction_ML_Syntax.mlty ->
      FStarC_Extraction_ML_Syntax.mlty ->
        FStarC_Extraction_Krml.decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun tag ->
      fun fields ->
        FStarC_Compiler_Util.print_endline "Parsing struct definition.";
        (let uu___1 = lident_of_typestring tag in
         match uu___1 with
         | FStar_Pervasives_Native.None ->
             ((let uu___3 =
                 FStarC_Extraction_ML_Code.string_of_mlty ([], "") tag in
               FStarC_Compiler_Util.print1
                 "Failed to parse struct tag from %s.\n" uu___3);
              FStar_Pervasives_Native.None)
         | FStar_Pervasives_Native.Some p ->
             define_struct_gen env p [] fields)
let (define_union_gen :
  FStarC_Extraction_Krml.env ->
    (Prims.string Prims.list * Prims.string) ->
      Prims.string Prims.list ->
        FStarC_Extraction_ML_Syntax.mlty ->
          FStarC_Extraction_Krml.decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun p ->
      fun args ->
        fun fields ->
          let env1 =
            FStarC_Compiler_List.fold_left
              (fun env2 ->
                 fun name -> FStarC_Extraction_Krml.extend_t env2 name) env
              args in
          let fields1 =
            let uu___ = parse_steel_c_fields env1 fields in
            FStarC_Compiler_Util.must uu___ in
          FStar_Pervasives_Native.Some
            (FStarC_Extraction_Krml.DUntaggedUnion
               (p, [], (FStarC_Compiler_List.length args), fields1))
let (define_union :
  FStarC_Extraction_Krml.env ->
    FStarC_Extraction_ML_Syntax.mlty ->
      FStarC_Extraction_ML_Syntax.mlty ->
        FStarC_Extraction_Krml.decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun tag ->
      fun fields ->
        FStarC_Compiler_Util.print_endline "Parsing union definition.";
        (let uu___1 = lident_of_typestring tag in
         match uu___1 with
         | FStar_Pervasives_Native.None ->
             ((let uu___3 =
                 FStarC_Extraction_ML_Code.string_of_mlty ([], "") tag in
               FStarC_Compiler_Util.print1
                 "Failed to parse union tag from %s.\n" uu___3);
              FStar_Pervasives_Native.None)
         | FStar_Pervasives_Native.Some p -> define_union_gen env p [] fields)
let (my_type_decls : unit -> unit) =
  fun uu___ ->
    FStarC_Extraction_Krml.register_pre_translate_type_decl
      (fun env ->
         fun ty ->
           match ty with
           | { FStarC_Extraction_ML_Syntax.tydecl_assumed = uu___1;
               FStarC_Extraction_ML_Syntax.tydecl_name = uu___2;
               FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___3;
               FStarC_Extraction_ML_Syntax.tydecl_parameters = uu___4;
               FStarC_Extraction_ML_Syntax.tydecl_meta = uu___5;
               FStarC_Extraction_ML_Syntax.tydecl_defn =
                 FStar_Pervasives_Native.Some
                 (FStarC_Extraction_ML_Syntax.MLTD_Abbrev
                 (FStarC_Extraction_ML_Syntax.MLTY_Named
                 (tag::fields::uu___6::uu___7::[], p)));_}
               when
               let uu___8 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___8 = "Steel.ST.C.Types.Struct.define_struct0" ->
               define_struct env tag fields
           | { FStarC_Extraction_ML_Syntax.tydecl_assumed = uu___1;
               FStarC_Extraction_ML_Syntax.tydecl_name = uu___2;
               FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___3;
               FStarC_Extraction_ML_Syntax.tydecl_parameters = uu___4;
               FStarC_Extraction_ML_Syntax.tydecl_meta = uu___5;
               FStarC_Extraction_ML_Syntax.tydecl_defn =
                 FStar_Pervasives_Native.Some
                 (FStarC_Extraction_ML_Syntax.MLTD_Abbrev
                 (FStarC_Extraction_ML_Syntax.MLTY_Named
                 (tag::fields::uu___6::uu___7::[], p)));_}
               when
               let uu___8 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___8 = "Steel.ST.C.Types.Union.define_union0" ->
               define_union env tag fields
           | { FStarC_Extraction_ML_Syntax.tydecl_assumed = uu___1;
               FStarC_Extraction_ML_Syntax.tydecl_name = name;
               FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___2;
               FStarC_Extraction_ML_Syntax.tydecl_parameters = args;
               FStarC_Extraction_ML_Syntax.tydecl_meta = uu___3;
               FStarC_Extraction_ML_Syntax.tydecl_defn =
                 FStar_Pervasives_Native.Some
                 (FStarC_Extraction_ML_Syntax.MLTD_Abbrev
                 (FStarC_Extraction_ML_Syntax.MLTY_Named
                 (uu___4::fields::uu___5::uu___6::[], p)));_}
               when
               let uu___7 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___7 = "Steel.ST.C.Types.Struct.struct_t0" ->
               let name1 = ((env.FStarC_Extraction_Krml.module_name), name) in
               let uu___7 = FStarC_Extraction_ML_Syntax.ty_param_names args in
               define_struct_gen env name1 uu___7 fields
           | { FStarC_Extraction_ML_Syntax.tydecl_assumed = uu___1;
               FStarC_Extraction_ML_Syntax.tydecl_name = name;
               FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___2;
               FStarC_Extraction_ML_Syntax.tydecl_parameters = args;
               FStarC_Extraction_ML_Syntax.tydecl_meta = uu___3;
               FStarC_Extraction_ML_Syntax.tydecl_defn =
                 FStar_Pervasives_Native.Some
                 (FStarC_Extraction_ML_Syntax.MLTD_Abbrev
                 (FStarC_Extraction_ML_Syntax.MLTY_Named
                 (uu___4::fields::uu___5::uu___6::[], p)));_}
               when
               let uu___7 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___7 = "Steel.ST.C.Types.Union.union_t0" ->
               let name1 = ((env.FStarC_Extraction_Krml.module_name), name) in
               let uu___7 = FStarC_Extraction_ML_Syntax.ty_param_names args in
               define_union_gen env name1 uu___7 fields
           | uu___1 ->
               FStarC_Compiler_Effect.raise
                 FStarC_Extraction_Krml.NotSupportedByKrmlExtension)
let (uu___0 : unit) =
  my_types_without_decay (); my_types (); my_exprs (); my_type_decls ()