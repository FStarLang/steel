%{
(*
Warning: 6 states have shift/reduce conflicts.
Warning: 8 shift/reduce conflicts were arbitrarily resolved.
Warning: 221 end-of-stream conflicts were arbitrarily resolved.
*)
(* (c) Microsoft Corporation. All rights reserved *)
open Prims
open FStar_Pervasives
open FStar_Errors
open FStar_Compiler_List
open FStar_Compiler_Util
open FStar_Compiler_Range
open FStar_Options
(* TODO : these files should be deprecated and removed *)
open FStar_Syntax_Syntax
open FStar_Parser_Const
open FStar_Syntax_Util
open FStar_Parser_AST
open FStar_Parser_Util
open FStar_Const
open FStar_Ident
open FStar_String
module PulseSyntaxExtension_Sugar = PulseSyntaxExtension_Sugar

let mk_meta_tac m = Meta m

let old_attribute_syntax_warning =
  "The `[@ ...]` syntax of attributes is deprecated. \
   Use `[@@ a1; a2; ...; an]`, a semi-colon separated list of attributes, instead"

let do_notation_deprecation_warning = "The lightweight do notation [x <-- y; z] or [x ;; z] is deprecated, use let operators (i.e. [let* x = y in z] or [y ;* z], [*] being any sequence of operator characters) instead."

let none_to_empty_list x =
  match x with
  | None -> []
  | Some l -> l

let as_aqual (q:unit option) =
    match q with
    | None -> None
    | Some _ -> Some Implicit

let pos_of_lexpos (p:Lexing.position) = FStar_Parser_Util.pos_of_lexpos p

let default_return =
    gen dummyRange,
    mk_term (Var (lid_of_ids [(mk_ident("unit", dummyRange))])) dummyRange Un

let with_computation_tag (c:PulseSyntaxExtension_Sugar.computation_type) t =
  match t with
  | None -> c
  | Some t -> { c with tag = t }

let rng p1 p2 = FStar_Parser_Util.mksyn_range p1 p2
let r p = rng (fst p) (snd p)
let mk_fn_defn q id is_rec bs body range =
    match body with
    | Inl (ascription, measure, body) ->
      let ascription = with_computation_tag ascription q in 
      PulseSyntaxExtension_Sugar.mk_fn_defn id is_rec (List.flatten bs) (Inl ascription) measure (Inl body) range

    | Inr (lambda, typ) ->
      PulseSyntaxExtension_Sugar.mk_fn_defn id is_rec (List.flatten bs) (Inr typ) None (Inr lambda) range

%}

/* pulse specific tokens; rest are inherited from F* */
%token MUT FN INVARIANT WHILE REF PARALLEL REWRITE FOLD GHOST ATOMIC EACH
%token WITH_INVS OPENS  SHOW_PROOF_STATE

%start pulseDecl
%start peekFnId
%type <PulseSyntaxExtension_Sugar.decl> pulseDecl
%type <string> peekFnId
%%

maybeRec:
  | REC
    { true }
  |
    { false }

/* This is to just peek at the name of the top-level definition */
peekFnId:
  | q=option(qual) FN maybeRec id=lident
      { FStar_Ident.string_of_id id }
  | q=option(qual) VAL FN id=lident
      { FStar_Ident.string_of_id id }

qual:
  | GHOST { PulseSyntaxExtension_Sugar.STGhost }
  | ATOMIC { PulseSyntaxExtension_Sugar.STAtomic }

/* This is the main entry point for the pulse parser */
pulseDecl:
  | q=option(qual)
    FN isRec=maybeRec lid=lident bs=pulseBinderList
    body=fnBody EOF
    {
      PulseSyntaxExtension_Sugar.FnDefn (mk_fn_defn q lid isRec bs body (rr $loc))
    }

  | q=option(qual)
    VAL FN isRec=maybeRec lid=lident bs=pulseBinderList
    ascription=pulseComputationType
    EOF
    {
      let open PulseSyntaxExtension_Sugar in
      let ascription = with_computation_tag ascription q in
      FnDecl (mk_fn_decl lid (List.flatten bs) (Inl ascription) (rr $loc))
    }

pulseBinderList:
  /* |  { [] } We don't yet support nullary functions */
  | bs=nonempty_list(multiBinder)
    {  bs }

localFnDefn:
  | q=option(qual) FN lid=lident
    bs=pulseBinderList
    body=fnBody
    {
      lid, mk_fn_defn q lid false bs body (rr $loc)
    }

fnBody:
  | ascription=pulseComputationType
    measure=option(DECREASES m=appTermNoRecordExp {m})
    LBRACE body=pulseStmt RBRACE
    {
      Inl (ascription, measure, body)
    }

  | COLON typ=option(appTerm) EQUALS lambda=pulseLambda
    { Inr (lambda, typ) }

pulseComputationType:
  | REQUIRES t=pulseVprop
    ret=option(RETURNS i=lidentOrUnderscore COLON r=term { (i, r) })
    ENSURES t2=pulseVprop
    maybe_opens=option(OPENS inv=appTermNoRecordExp { inv })
    {
        let i, r =
          match ret with
          | Some (i, r) -> i, r
          | None -> default_return
        in
        PulseSyntaxExtension_Sugar.mk_comp ST t i r t2 maybe_opens (rr $loc)
    }


pulseStmtNoSeq:
  | OPEN i=quident
    { PulseSyntaxExtension_Sugar.mk_open i }
  | tm=appTerm o=option(LARROW v=noSeqTerm { v })
    {
        match o, tm.tm with
        | None, _ ->
          PulseSyntaxExtension_Sugar.mk_expr tm

        | Some arr_elt, Op(op, [arr;ix]) when FStar_Ident.string_of_id op = ".()" ->
          PulseSyntaxExtension_Sugar.mk_array_assignment arr ix arr_elt

        | _ ->
          raise_error (Fatal_SyntaxError, "Expected an array assignment of the form x.(i) <- v") (rr $loc)
    }
  | lhs=appTermNoRecordExp COLON_EQUALS a=noSeqTerm
    { PulseSyntaxExtension_Sugar.mk_assignment lhs a }
  | LET q=option(mutOrRefQualifier) i=lidentOrUnderscore typOpt=option(preceded(COLON, appTerm)) EQUALS LBRACK_BAR v=noSeqTerm SEMICOLON n=noSeqTerm BAR_RBRACK
    { PulseSyntaxExtension_Sugar.mk_let_binding q i typOpt (Some (Array_initializer { init=v; len=n })) }
  | LET q=option(mutOrRefQualifier) i=lidentOrUnderscore typOpt=option(preceded(COLON, appTerm)) EQUALS tm=noSeqTerm
    { PulseSyntaxExtension_Sugar.mk_let_binding q i typOpt (Some (Default_initializer tm)) }
  | LBRACE s=pulseStmt RBRACE
    { PulseSyntaxExtension_Sugar.mk_block s }
  | s=ifStmt
    { s }
  | MATCH tm=appTermNoRecordExp c=option(ensuresVprop) LBRACE brs=list(pulseMatchBranch) RBRACE
    { PulseSyntaxExtension_Sugar.mk_match tm c brs }
  | WHILE LPAREN tm=pulseStmt RPAREN INVARIANT i=lident DOT v=pulseVprop LBRACE body=pulseStmt RBRACE
    { PulseSyntaxExtension_Sugar.mk_while tm i v body }
  | INTRO p=pulseVprop WITH ws=nonempty_list(indexingTerm)
    { PulseSyntaxExtension_Sugar.mk_intro p ws }
  | PARALLEL REQUIRES p1=pulseVprop AND p2=pulseVprop
             ENSURES q1=pulseVprop AND q2=pulseVprop
             LBRACE b1=pulseStmt RBRACE
             LBRACE b2=pulseStmt RBRACE
    { PulseSyntaxExtension_Sugar.mk_par p1 p2 q1 q2 b1 b2 }
  | bs=withBindersOpt REWRITE body=rewriteBody
    {
        PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders body bs
    }
  | bs=withBindersOpt ASSERT p=pulseVprop
    { PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders (ASSERT p) bs }
  | bs=withBindersOpt UNFOLD ns=option(names) p=pulseVprop
    { PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders (UNFOLD (ns,p)) bs }
  | bs=withBindersOpt FOLD ns=option(names) p=pulseVprop
    { PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders (FOLD (ns,p)) bs }
  | bs=withBinders UNDERSCORE
    { PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders WILD bs }
  | SHOW_PROOF_STATE
    { PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders (SHOW_PROOF_STATE (rr $loc)) [] }
  | WITH_INVS names=nonempty_list(atomicTerm) r=option(ensuresVprop) LBRACE body=pulseStmt RBRACE
    { PulseSyntaxExtension_Sugar.mk_with_invs names body r }
  | f=localFnDefn
    {
      let id, fndecl = f in
      PulseSyntaxExtension_Sugar.mk_let_binding None id None (Some (Lambda_initializer fndecl))
    }

pulseLambda:
  | bs=pulseBinderList
    ascription=option(pulseComputationType)
    LBRACE body=pulseStmt RBRACE
    {
      PulseSyntaxExtension_Sugar.mk_lambda (List.flatten bs) ascription body (rr ($loc))
    }

rewriteBody:
  | EACH pairs=separated_nonempty_list (COMMA, x=appTerm AS y=appTerm { (x, y)}) goal=option(IN t=pulseVprop { t })
    { RENAME(pairs, goal) }
  | p1=pulseVprop AS p2=pulseVprop
    { PulseSyntaxExtension_Sugar.REWRITE(p1, p2) }

names:
  | LBRACK l=separated_nonempty_list(SEMICOLON, qlident) RBRACK
    { l }

withBinders:
  | WITH bs=nonempty_list(multiBinder) DOT
    { List.flatten bs }

withBindersOpt:
  | w=withBinders
    { w }
  | { [] }

ensuresVprop:
  | ENSURES s=pulseVprop
    { s }

pulseMatchBranch:
  | pat=pulsePattern RARROW LBRACE e=pulseStmt RBRACE
    { (pat, e) }

pulsePattern:
  | p=tuplePattern { p }

pulseStmt:
  | s=pulseStmtNoSeq
    { PulseSyntaxExtension_Sugar.mk_stmt s (rr $loc) }
  | s1=pulseStmtNoSeq SEMICOLON s2=option(pulseStmt)
    {
      let s1 = PulseSyntaxExtension_Sugar.mk_stmt s1 (rr ($loc(s1))) in
      match s2 with
      | None -> s1
      | Some s2 -> PulseSyntaxExtension_Sugar.mk_stmt (PulseSyntaxExtension_Sugar.mk_sequence s1 s2) (rr ($loc))
    }

ifStmt:
  | IF tm=appTermNoRecordExp vp=option(ensuresVprop) LBRACE th=pulseStmt RBRACE e=option(elseBlock)
    { PulseSyntaxExtension_Sugar.mk_if tm vp th e }

elseBlock:
  | ELSE LBRACE p=pulseStmt RBRACE
    { p }
  | ELSE s=ifStmt
    { PulseSyntaxExtension_Sugar.mk_stmt s (rr $loc) }

mutOrRefQualifier:
  | MUT { MUT }
  | REF { REF }

pulseVprop:
  | p=typX(tmEqWith(appTermNoRecordExp), tmEqWith(appTermNoRecordExp))
    { PulseSyntaxExtension_Sugar.(as_vprop (VPropTerm p) (rr $loc)) }
