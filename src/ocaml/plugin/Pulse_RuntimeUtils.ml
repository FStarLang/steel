type context = ((string * FStar_Range.range option) list) FStar_Sealed.sealed
let extend_context (s:string) (r:FStar_Range.range option) (c:context) = (s,r)::c
let print_exn (e:exn) = Printexc.to_string e
let debug_at_level_no_module (s:string) = FStar_Options.debug_at_level_no_module (FStar_Options.Other s)
let debug_at_level (g:FStar_Reflection_Types.env) (s:string) = FStar_TypeChecker_Env.debug g (FStar_Options.Other s)
let bv_set_range (bv:FStar_Syntax_Syntax.bv) (r:FStar_Range.range) = FStar_Syntax_Syntax.set_range_of_bv bv r
let bv_range (bv:FStar_Syntax_Syntax.bv) = FStar_Syntax_Syntax.range_of_bv bv
let binder_set_range (b:FStar_Syntax_Syntax.binder) (r:FStar_Range.range) =
    { b with FStar_Syntax_Syntax.binder_bv = (bv_set_range b.FStar_Syntax_Syntax.binder_bv r) }
let binder_range (b:FStar_Syntax_Syntax.binder) = bv_range b.FStar_Syntax_Syntax.binder_bv
let set_range (t:FStar_Syntax_Syntax.term) (r:FStar_Range.range) = { t with FStar_Syntax_Syntax.pos = r}
let set_use_range (t:FStar_Syntax_Syntax.term) (r:FStar_Range.range) = FStar_Syntax_Subst.set_use_range r t
let error_code_uninstantiated_variable () = FStar_Errors.errno FStar_Errors_Codes.Error_UninstantiatedUnificationVarInTactic
let is_range_zero (r:FStar_Range.range) = r = FStar_Range.range_0
let union_ranges (r0:FStar_Range.range) (r1:FStar_Range.range) = FStar_Compiler_Range.union_ranges r0 r1
let range_of_term (t:FStar_Syntax_Syntax.term) = t.FStar_Syntax_Syntax.pos
let unfold_def (g:FStar_Reflection_Types.env) (head:string) (names:string list) (t:FStar_Syntax_Syntax.term) : FStar_Syntax_Syntax.term option =
    let open FStar_TypeChecker_Env in
    Some (FStar_TypeChecker_Normalize.normalize
            [Beta; Iota;
             UnfoldOnly (FStar_Ident.lid_of_str head::List.map FStar_Ident.lid_of_str names)] g t)