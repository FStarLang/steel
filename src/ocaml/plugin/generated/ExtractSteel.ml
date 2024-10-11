open Prims
let (steel_translate_type_without_decay :
  FStarC_Extraction_Krml.translate_type_without_decay_t) =
  fun env ->
    fun t ->
      match t with
      | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Steel.TLArray.t" ->
          let uu___ =
            FStarC_Extraction_Krml.translate_type_without_decay env arg in
          FStarC_Extraction_Krml.TConstBuf uu___
      | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let p1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          ((p1 = "Steel.Reference.ref") || (p1 = "Steel.ST.Reference.ref"))
            || (p1 = "Steel.ST.HigherArray.ptr")
          ->
          let uu___ =
            FStarC_Extraction_Krml.translate_type_without_decay env arg in
          FStarC_Extraction_Krml.TBuf uu___
      | uu___ ->
          FStarC_Compiler_Effect.raise
            FStarC_Extraction_Krml.NotSupportedByKrmlExtension
let (flatten_app :
  FStarC_Extraction_ML_Syntax.mlexpr -> FStarC_Extraction_ML_Syntax.mlexpr) =
  fun e ->
    let rec aux args e1 =
      match e1.FStarC_Extraction_ML_Syntax.expr with
      | FStarC_Extraction_ML_Syntax.MLE_App (head, args0) ->
          aux (FStarC_Compiler_List.op_At args0 args) head
      | uu___ ->
          (match args with
           | [] -> e1
           | uu___1 ->
               {
                 FStarC_Extraction_ML_Syntax.expr =
                   (FStarC_Extraction_ML_Syntax.MLE_App (e1, args));
                 FStarC_Extraction_ML_Syntax.mlty =
                   (e1.FStarC_Extraction_ML_Syntax.mlty);
                 FStarC_Extraction_ML_Syntax.loc =
                   (e1.FStarC_Extraction_ML_Syntax.loc)
               }) in
    aux [] e
let (steel_translate_expr : FStarC_Extraction_Krml.translate_expr_t) =
  fun env ->
    fun e ->
      let e1 = flatten_app e in
      match e1.FStarC_Extraction_ML_Syntax.expr with
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_},
           uu___4)
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.null_ptr" ->
          let uu___5 = FStarC_Extraction_Krml.translate_type env t in
          FStarC_Extraction_Krml.EBufNull uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_},
           arg::[])
          when
          let uu___4 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___4 = "Steel.ST.HigherArray.is_null_ptr" ->
          let uu___4 = FStarC_Extraction_Krml.translate_type env t in
          let uu___5 = FStarC_Extraction_Krml.translate_expr env arg in
          FStarC_Extraction_Krml.generate_is_null uu___4 uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _perm0::_perm1::_seq0::_seq1::e0::_len0::e11::_len1::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.ptrdiff_ptr" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env e0 in
            let uu___7 = FStarC_Extraction_Krml.translate_expr env e11 in
            (uu___6, uu___7) in
          FStarC_Extraction_Krml.EBufDiff uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e11::e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.TLArray.get" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStarC_Extraction_Krml.translate_expr env e2 in
            (uu___6, uu___7) in
          FStarC_Extraction_Krml.EBufRead uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _perm::e11::_len::_seq::e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.index_ptr" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStarC_Extraction_Krml.translate_expr env e2 in
            (uu___6, uu___7) in
          FStarC_Extraction_Krml.EBufRead uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.Reference.read" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env e2 in
            (uu___6,
              (FStarC_Extraction_Krml.EQualified (["C"], "_zero_for_deref"))) in
          FStarC_Extraction_Krml.EBufRead uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _perm::_v::e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.Reference.read" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env e2 in
            (uu___6,
              (FStarC_Extraction_Krml.EQualified (["C"], "_zero_for_deref"))) in
          FStarC_Extraction_Krml.EBufRead uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           init::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.Reference._alloca" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env init in
            (FStarC_Extraction_Krml.Stack, uu___6,
              (FStarC_Extraction_Krml.EConstant
                 (FStarC_Extraction_Krml.UInt32, "1"))) in
          FStarC_Extraction_Krml.EBufCreate uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           init::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "Steel.Reference.malloc") ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.ST.Reference.alloc")
          ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env init in
            (FStarC_Extraction_Krml.ManuallyManaged, uu___6,
              (FStarC_Extraction_Krml.EConstant
                 (FStarC_Extraction_Krml.UInt32, "1"))) in
          FStarC_Extraction_Krml.EBufCreate uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e0::e11::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.malloc_ptr" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env e0 in
            let uu___7 = FStarC_Extraction_Krml.translate_expr env e11 in
            (FStarC_Extraction_Krml.ManuallyManaged, uu___6, uu___7) in
          FStarC_Extraction_Krml.EBufCreate uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.Reference.free" ->
          let uu___5 = FStarC_Extraction_Krml.translate_expr env e2 in
          FStarC_Extraction_Krml.EBufFree uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _v::e2::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "Steel.ST.HigherArray.free_ptr") ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.ST.Reference.free")
          ->
          let uu___5 = FStarC_Extraction_Krml.translate_expr env e2 in
          FStarC_Extraction_Krml.EBufFree uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e11::e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.ptr_shift" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStarC_Extraction_Krml.translate_expr env e2 in
            (uu___6, uu___7) in
          FStarC_Extraction_Krml.EBufSub uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e11::_len::_s::e2::e3::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.upd_ptr" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStarC_Extraction_Krml.translate_expr env e2 in
            let uu___8 = FStarC_Extraction_Krml.translate_expr env e3 in
            (uu___6, uu___7, uu___8) in
          FStarC_Extraction_Krml.EBufWrite uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e11::_len::_s::e2::e3::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.upd_ptr" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStarC_Extraction_Krml.translate_expr env e2 in
            let uu___8 = FStarC_Extraction_Krml.translate_expr env e3 in
            (uu___6, uu___7, uu___8) in
          FStarC_Extraction_Krml.EBufWrite uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e11::e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.Reference.write" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStarC_Extraction_Krml.translate_expr env e2 in
            (uu___6,
              (FStarC_Extraction_Krml.EQualified (["C"], "_zero_for_deref")),
              uu___7) in
          FStarC_Extraction_Krml.EBufWrite uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _v::e11::e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.Reference.write" ->
          let uu___5 =
            let uu___6 = FStarC_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStarC_Extraction_Krml.translate_expr env e2 in
            (uu___6,
              (FStarC_Extraction_Krml.EQualified (["C"], "_zero_for_deref")),
              uu___7) in
          FStarC_Extraction_Krml.EBufWrite uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name p;
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           uu___2::[])
          when
          let uu___3 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___3 = "Steel.ST.Reference._push_frame" ->
          FStarC_Extraction_Krml.EPushFrame
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5::uu___6::[])
          when
          let uu___7 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___7 = "Steel.ST.Reference._free_and_pop_frame" ->
          FStarC_Extraction_Krml.EPopFrame
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5::uu___6::uu___7::e11::uu___8::e2::e3::uu___9::e4::e5::[])
          when
          let uu___10 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___10 = "Steel.ST.HigherArray.blit_ptr" ->
          let uu___10 =
            let uu___11 = FStarC_Extraction_Krml.translate_expr env e11 in
            let uu___12 = FStarC_Extraction_Krml.translate_expr env e2 in
            let uu___13 = FStarC_Extraction_Krml.translate_expr env e3 in
            let uu___14 = FStarC_Extraction_Krml.translate_expr env e4 in
            let uu___15 = FStarC_Extraction_Krml.translate_expr env e5 in
            (uu___11, uu___12, uu___13, uu___14, uu___15) in
          FStarC_Extraction_Krml.EBufBlit uu___10
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5::uu___6::e2::[])
          when
          let uu___7 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___7 = "Steel.Effect.Atomic.return" ->
          FStarC_Extraction_Krml.translate_expr env e2
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name p;
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           _inv::test::body::[])
          when
          let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___2 = "Steel.ST.Loops.while_loop" ->
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Extraction_Krml.translate_expr env test in
                let uu___6 =
                  let uu___7 = FStarC_Extraction_Krml.translate_expr env body in
                  [uu___7] in
                uu___5 :: uu___6 in
              FStarC_Extraction_Krml.EUnit :: uu___4 in
            ((FStarC_Extraction_Krml.EQualified
                (["Steel"; "Loops"], "while_loop")), uu___3) in
          FStarC_Extraction_Krml.EApp uu___2
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name
               ("Steel"::"ST"::"Printf"::[], fn);
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           args)
          ->
          let uu___2 =
            let uu___3 =
              FStarC_Compiler_List.map
                (FStarC_Extraction_Krml.translate_expr env) args in
            ((FStarC_Extraction_Krml.EQualified (["LowStar"; "Printf"], fn)),
              uu___3) in
          FStarC_Extraction_Krml.EApp uu___2
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5::uu___6::e2::[])
          when
          (let uu___7 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___7 = "Steel.Effect.Atomic.return") ||
            (let uu___7 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___7 = "Steel.ST.Util.return")
          -> FStarC_Extraction_Krml.translate_expr env e2
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _fp::_fp'::_opened::_p::_i::{
                                         FStarC_Extraction_ML_Syntax.expr =
                                           FStarC_Extraction_ML_Syntax.MLE_Fun
                                           (uu___5, body);
                                         FStarC_Extraction_ML_Syntax.mlty =
                                           uu___6;
                                         FStarC_Extraction_ML_Syntax.loc =
                                           uu___7;_}::[])
          when
          (let uu___8 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___8 = "Steel.ST.Util.with_invariant") ||
            (let uu___8 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___8 = "Steel.Effect.Atomic.with_invariant")
          -> FStarC_Extraction_Krml.translate_expr env body
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _fp::_fp'::_opened::_p::_i::e2::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "Steel.ST.Util.with_invariant") ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.Effect.Atomic.with_invariant")
          ->
          let uu___5 =
            let uu___6 =
              FStarC_Compiler_Util.string_of_int
                (FStar_Pervasives_Native.fst
                   e2.FStarC_Extraction_ML_Syntax.loc) in
            FStarC_Compiler_Util.format2
              "Extraction of with_invariant requires its argument to be a function literal at extraction time, try marking its argument inline_for_extraction (%s, %s)"
              uu___6
              (FStar_Pervasives_Native.snd e2.FStarC_Extraction_ML_Syntax.loc) in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_ExtractionUnsupported ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___5)
      | uu___ ->
          FStarC_Compiler_Effect.raise
            FStarC_Extraction_Krml.NotSupportedByKrmlExtension
let (steel_translate_let : FStarC_Extraction_Krml.translate_let_t) =
  fun env ->
    fun flavor ->
      fun lb ->
        match lb with
        | { FStarC_Extraction_ML_Syntax.mllb_name = name;
            FStarC_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t);
            FStarC_Extraction_ML_Syntax.mllb_add_unit = uu___;
            FStarC_Extraction_ML_Syntax.mllb_def =
              {
                FStarC_Extraction_ML_Syntax.expr =
                  FStarC_Extraction_ML_Syntax.MLE_App
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
                   l::[]);
                FStarC_Extraction_ML_Syntax.mlty = uu___6;
                FStarC_Extraction_ML_Syntax.loc = uu___7;_};
            FStarC_Extraction_ML_Syntax.mllb_attrs = uu___8;
            FStarC_Extraction_ML_Syntax.mllb_meta = meta;
            FStarC_Extraction_ML_Syntax.print_typ = uu___9;_} when
            let uu___10 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
            uu___10 = "Steel.TLArray.create" ->
            if
              FStarC_Compiler_List.mem FStarC_Extraction_ML_Syntax.NoExtract
                meta
            then FStar_Pervasives_Native.None
            else
              (let meta1 = FStarC_Extraction_Krml.translate_flags meta in
               let env1 =
                 let uu___11 =
                   FStarC_Extraction_ML_Syntax.ty_param_names tvars in
                 FStarC_Compiler_List.fold_left
                   (fun env2 ->
                      fun name1 -> FStarC_Extraction_Krml.extend_t env2 name1)
                   env uu___11 in
               let t1 = FStarC_Extraction_Krml.translate_type env1 t in
               let name1 = ((env1.FStarC_Extraction_Krml.module_name), name) in
               try
                 (fun uu___11 ->
                    match () with
                    | () ->
                        let expr =
                          let uu___12 = FStarC_Extraction_Krml.list_elements l in
                          FStarC_Compiler_List.map
                            (FStarC_Extraction_Krml.translate_expr env1)
                            uu___12 in
                        FStar_Pervasives_Native.Some
                          (FStarC_Extraction_Krml.DGlobal
                             (meta1, name1,
                               (FStarC_Compiler_List.length tvars), t1,
                               (FStarC_Extraction_Krml.EBufCreateL
                                  (FStarC_Extraction_Krml.Eternal, expr)))))
                   ()
               with
               | uu___11 ->
                   ((let uu___13 =
                       let uu___14 =
                         FStarC_Extraction_ML_Syntax.string_of_mlpath name1 in
                       let uu___15 = FStarC_Compiler_Util.print_exn uu___11 in
                       FStarC_Compiler_Util.format2
                         "Error extracting %s to KaRaMeL (%s)\n" uu___14
                         uu___15 in
                     FStarC_Errors.log_issue0
                       FStarC_Errors_Codes.Warning_DefinitionNotTranslated ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                       (Obj.magic uu___13));
                    FStar_Pervasives_Native.Some
                      (FStarC_Extraction_Krml.DGlobal
                         (meta1, name1, (FStarC_Compiler_List.length tvars),
                           t1, FStarC_Extraction_Krml.EAny))))
        | uu___ ->
            FStarC_Compiler_Effect.raise
              FStarC_Extraction_Krml.NotSupportedByKrmlExtension
let (uu___0 : unit) =
  FStarC_Extraction_Krml.register_pre_translate_type_without_decay
    steel_translate_type_without_decay;
  FStarC_Extraction_Krml.register_pre_translate_expr steel_translate_expr;
  FStarC_Extraction_Krml.register_pre_translate_let steel_translate_let