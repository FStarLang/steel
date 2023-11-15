%{
(*
 We are expected to have only 6 shift-reduce conflicts in ML and 8 in F#.
 A lot (222) of end-of-stream conflicts are also reported and
 should be investigated...
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

let with_computation_tag (c:PulseSugar.computation_type) t =
  match t with
  | None -> c
  | Some t -> { c with tag = t }

let rng p1 p2 = FStar_Parser_Util.mksyn_range p1 p2
let r p = rng (fst p) (snd p)

%}

/* pulse specific tokens; rest are inherited from F* */
%token MUT FN INVARIANT WHILE REF PARALLEL REWRITE FOLD GHOST ATOMIC EACH
%token WITH_INVS OPENS

%start pulseDecl
%start peekFnId
%type <PulseSugar.decl> pulseDecl
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

qual:
  | GHOST { PulseSugar.STGhost }
  | ATOMIC { PulseSugar.STAtomic }

/* This is the main entry point for the pulse parser */
pulseDecl:
  | q=option(qual)
    FN isRec=maybeRec lid=lident bs=nonempty_list(pulseMultiBinder)
    ascription=pulseComputationType
    measure=option(DECREASES m=appTermNoRecordExp {m})
    LBRACE body=pulseStmt RBRACE
    {
      let ascription = with_computation_tag ascription q in
      PulseSugar.mk_fn_decl lid isRec (List.flatten bs) ascription measure body (rr $loc)
    }

pulseMultiBinder:
  | LPAREN qual_ids=nonempty_list(q=option(HASH) id=lidentOrUnderscore { (q, id) }) COLON t=appTerm RPAREN
    { List.map (fun (q, id) -> (as_aqual q, id, t)) qual_ids }
  | q=option(HASH) id=lidentOrUnderscore
    { [(as_aqual q, id, mk_term Wild (rr ($loc(id))) Un)] }

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
        PulseSugar.mk_comp ST t i r t2 maybe_opens (rr $loc)
    }


pulseStmtNoSeq:
  | OPEN i=quident
    { PulseSugar.mk_open i }
  | tm=appTerm o=option(LARROW v=noSeqTerm { v })
    {
        match o, tm.tm with
        | None, _ ->
          PulseSugar.mk_expr tm

        | Some arr_elt, Op(op, [arr;ix]) when FStar_Ident.string_of_id op = ".()" ->
          PulseSugar.mk_array_assignment arr ix arr_elt

        | _ ->
          raise_error (Fatal_SyntaxError, "Expected an array assignment of the form x.(i) <- v") (rr $loc)
    }
  | lhs=appTermNoRecordExp COLON_EQUALS a=noSeqTerm
    { PulseSugar.mk_assignment lhs a }
  | LET q=option(mutOrRefQualifier) i=lident typOpt=option(preceded(COLON, appTerm)) EQUALS LBRACK_BAR v=noSeqTerm SEMICOLON n=noSeqTerm BAR_RBRACK
    { PulseSugar.mk_let_binding q i typOpt (Some (Array_initializer { init=v; len=n })) }
  | LET q=option(mutOrRefQualifier) i=lident typOpt=option(preceded(COLON, appTerm)) EQUALS tm=noSeqTerm
    { PulseSugar.mk_let_binding q i typOpt (Some (Default_initializer tm)) }
  | LBRACE s=pulseStmt RBRACE
    { PulseSugar.mk_block s }
  | s=ifStmt
    { s }
  | MATCH tm=appTermNoRecordExp c=option(ensuresVprop) LBRACE brs=list(pulseMatchBranch) RBRACE
    { PulseSugar.mk_match tm c brs }
  | WHILE LPAREN tm=pulseStmt RPAREN INVARIANT i=lident DOT v=pulseVprop LBRACE body=pulseStmt RBRACE
    { PulseSugar.mk_while tm i v body }
  | INTRO p=pulseVprop WITH ws=nonempty_list(indexingTerm)
    { PulseSugar.mk_intro p ws }
  | PARALLEL REQUIRES p1=pulseVprop AND p2=pulseVprop
             ENSURES q1=pulseVprop AND q2=pulseVprop
             LBRACE b1=pulseStmt RBRACE
             LBRACE b2=pulseStmt RBRACE
    { PulseSugar.mk_par p1 p2 q1 q2 b1 b2 }
  | bs=withBindersOpt REWRITE body=rewriteBody
    {
        PulseSugar.mk_proof_hint_with_binders body bs
    }
  | bs=withBindersOpt ASSERT p=pulseVprop
    { PulseSugar.mk_proof_hint_with_binders (ASSERT p) bs }
  | bs=withBindersOpt UNFOLD ns=option(names) p=pulseVprop
    { PulseSugar.mk_proof_hint_with_binders (UNFOLD (ns,p)) bs }
  | bs=withBindersOpt FOLD ns=option(names) p=pulseVprop
    { PulseSugar.mk_proof_hint_with_binders (FOLD (ns,p)) bs }
  | WITH_INVS names=nonempty_list(atomicTerm) r=option(ensuresVprop) LBRACE body=pulseStmt RBRACE
    { PulseSugar.mk_with_invs names body r }

rewriteBody:
  | EACH pairs=separated_nonempty_list (COMMA, x=appTerm AS y=appTerm { (x, y)}) goal=option(IN t=pulseVprop { t })
    { RENAME(pairs, goal) }
  | p1=pulseVprop AS p2=pulseVprop
    { PulseSugar.REWRITE(p1, p2) }

names:
  | LBRACK l=separated_nonempty_list(SEMICOLON, qlident) RBRACK
    { l }

withBindersOpt:
  | WITH bs=nonempty_list(pulseMultiBinder) DOT
    { List.flatten bs }
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
    { PulseSugar.mk_stmt s (rr $loc) }
  | s1=pulseStmtNoSeq SEMICOLON s2=option(pulseStmt)
    {
      let s1 = PulseSugar.mk_stmt s1 (rr ($loc(s1))) in
      match s2 with
      | None -> s1
      | Some s2 -> PulseSugar.mk_stmt (PulseSugar.mk_sequence s1 s2) (rr ($loc))
    }

ifStmt:
  | IF tm=appTermNoRecordExp vp=option(ensuresVprop) LBRACE th=pulseStmt RBRACE e=option(elseBlock)
    { PulseSugar.mk_if tm vp th e }

elseBlock:
  | ELSE LBRACE p=pulseStmt RBRACE
    { p }
  | ELSE s=ifStmt
    { PulseSugar.mk_stmt s (rr $loc) }

mutOrRefQualifier:
  | MUT { MUT }
  | REF { REF }

maybeHash:
  |      { Nothing }
  | HASH { Hash }

atomicVprop:
  | LPAREN p=pulseVprop RPAREN
    { p }
  | BACKTICK_AT p=atomicTerm
    { PulseSugar.(as_vprop (VPropTerm p) (rr $loc)) }
  | head=qlident args=list(argTerm)
    {
      let head = mk_term (Var head) (rr $loc(head)) Un in
      let app = mkApp head (map (fun (x,y) -> (y,x)) args) (rr2 $loc(head) $loc(args)) in
      PulseSugar.(as_vprop (VPropTerm app) (rr $loc))
    }

%inline
starOp:
  | o=OPINFIX3
    { if o = "**" then () else raise_error (Fatal_SyntaxError, "Unexpected infix operator; expected '**'") (rr $loc) }
  | BACKTICK id=IDENT BACKTICK
    { if id = "star" then () else raise_error (Fatal_SyntaxError, "Unexpected infix operator; expected '**'") (rr $loc) }


pulseVprop:
  | t=atomicVprop
    { t }
  | EXISTS bs=nonempty_list(pulseMultiBinder) DOT body=pulseVprop
    { PulseSugar.(as_vprop (mk_vprop_exists (List.flatten bs) body) (rr $loc)) }
  | l=pulseVprop starOp r=pulseVprop
    {  PulseSugar.(as_vprop (VPropStar (l, r)) (rr $loc)) }
