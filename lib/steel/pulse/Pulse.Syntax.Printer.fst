module Pulse.Syntax.Printer
open FStar.Printf
open Pulse.Syntax.Base

module L = FStar.List.Tot

module T = FStar.Tactics.V2
module Un = FStar.Sealed
module R = FStar.Reflection.V2

module RU = Pulse.RuntimeUtils

let tot_or_ghost_to_string = function
  | T.E_Total -> "total"
  | T.E_Ghost -> "ghost"


let name_to_string (f:R.name) = String.concat "." f

let dbg_printing : bool = true

// let constant_to_string = function
//   | Unit -> "()"
//   | Bool true -> "true"
//   | Bool false -> "false"
//   | Int i -> sprintf "%d" i

let rec universe_to_string (n:nat) (u:universe)
  : Tot string (decreases u) =
  let open R in
  match inspect_universe u with
  | Uv_Unk -> "_"
  | Uv_Zero -> sprintf "%d" n
  | Uv_Succ u -> universe_to_string (n + 1) u
  | Uv_BVar x -> if n = 0 then sprintf "%d" x else sprintf "(%d + %d)" x n
  | Uv_Max us ->
    let r = "(max _)" in
    // sprintf "(max %s %s)" (universe_to_string 0 u0) (universe_to_string 0 u1) in
    if n = 0 then r else sprintf "%s + %d" r n
  | _ -> sprintf "<univ>"

let univ_to_string u = sprintf "u#%s" (universe_to_string 0 u)
let qual_to_doc = function
  | None -> empty
  | Some Implicit -> doc_of_string "#"
let qual_to_string = function
  | None -> ""
  | Some Implicit -> "#"

let indent (level:string) = level ^ "\t"

let rec term_to_doc t
  : T.Tac document
  = match t.t with
    | Tm_Emp -> doc_of_string "emp"

    | Tm_Pure p -> doc_of_string "pure" ^/^ parens (term_to_doc p)
    | Tm_Star p1 p2 ->
      infix 2 1 (doc_of_string "**")
                (term_to_doc p1)
                (term_to_doc p2)

    | Tm_ExistsSL _ b body ->
      prefix 2 1 (
        group (prefix 2 1 (doc_of_string "exists")
                            (parens (doc_of_string (T.unseal b.binder_ppname.name)
                                                    ^^ doc_of_string ":"
                                                    ^^ term_to_doc b.binder_ty)))
                ^^ doc_of_string ".")
        (term_to_doc body)

    | Tm_ForallSL u b body ->
      prefix 2 1 (
        group (prefix 2 1 (doc_of_string "forall")
                            (parens (doc_of_string (T.unseal b.binder_ppname.name)
                                                    ^^ doc_of_string ":"
                                                    ^^ term_to_doc b.binder_ty)))
                ^^ doc_of_string ".")
        (term_to_doc body)

    | Tm_VProp -> doc_of_string "vprop"
    | Tm_Inames -> doc_of_string "inames"
    | Tm_EmpInames -> doc_of_string "emp_inames"

    | Tm_Unknown -> doc_of_string "_"
    | Tm_FStar t ->
      T.term_to_doc t

let term_to_string t = render (term_to_doc t)

let binder_to_doc (b:binder)
  : T.Tac document
  = doc_of_string (T.unseal b.binder_ppname.name) ^^ doc_of_string ":" ^^ term_to_doc b.binder_ty

let binder_to_string (b:binder)
  : T.Tac string
  = sprintf "%s:%s"
            (T.unseal b.binder_ppname.name)
            (term_to_string b.binder_ty)

let ctag_to_string = function
  | STT -> "ST"
  | STT_Atomic -> "STAtomic"
  | STT_Ghost -> "STGhost"

// FIXME: track whether parentheses are needed. Or can we somehow detect
// if a doc is atomic?
let comp_to_doc (c:comp)
  : T.Tac document
  = match c with
    | C_Tot t ->
      nest 2 (
      doc_of_string "Tot" ^/^ term_to_doc t
      )

    | C_ST s ->
      nest 2 (
      group (doc_of_string "stt" ^/^ term_to_doc s.res)
      ^/^ nest 2 (group (parens (doc_of_string "requires" ^/^ term_to_doc s.pre)))
      ^/^ nest 2 (group (parens (doc_of_string "ensures" ^/^ term_to_doc s.post)))
      )

    | C_STAtomic inames s ->
      nest 2 (
      group (doc_of_string "stt_atomic" ^/^ term_to_doc inames ^/^ term_to_doc s.res)
      ^/^ group (parens (doc_of_string "requires" ^/^ term_to_doc s.pre))
      ^/^ group (parens (doc_of_string "ensures" ^/^ term_to_doc s.post))
      )

    | C_STGhost inames s ->
      nest 2 (
      group (doc_of_string "stt_ghost" ^/^ term_to_doc inames ^/^ term_to_doc s.res)
      ^/^ nest 2 (group (parens (doc_of_string "requires" ^/^ term_to_doc s.pre)))
      ^/^ nest 2 (group (parens (doc_of_string "ensures" ^/^ term_to_doc s.post)))
      )

let comp_to_string c = render (comp_to_doc c)

let term_opt_to_string (t:option term)
  : T.Tac string
  = match t with
    | None -> ""
    | Some t -> term_to_string t

let term_list_to_string (sep:string) (t:list term)
  : T.Tac string
  = String.concat sep (T.map term_to_string t)

(* Need these since the combinators expect tot functions... *)
let separate_map (sep:document) (f : 'a -> T.Tac document) (l : list 'a) : T.Tac document =
  separate sep (T.map f l)

let braced (d:document) : document =
  surround 2 1 (doc_of_string "{") d (doc_of_string "}")

let rec st_term_to_doc (t:st_term)
  : T.Tac document
  = match t.term with
    | Tm_Return { ctag; insert_eq; term } ->
      group (
        doc_of_string (sprintf "return_%s%s"
                          (match ctag with
                          | STT -> "stt"
                          | STT_Atomic -> "stt_atomic"
                          | STT_Ghost -> "stt_ghost")
                          (if insert_eq then "" else "_noeq"))
        ^/^ term_to_doc term)

    | Tm_STApp {head; arg_qual; arg } ->
      parens (
        (if dbg_printing then doc_of_string "<stapp>" else empty)
        ^/^ term_to_doc head
        ^/^ qual_to_doc arg_qual ^^ term_to_doc arg
      )

    | Tm_Bind { binder; head; body } ->
      surround 2 1
        (group (surround 2 1 (doc_of_string "let") (binder_to_doc binder) (doc_of_string "=")))
        (st_term_to_doc head)
        (doc_of_string "in")
      ^/^ st_term_to_doc body

    | Tm_TotBind { head; binder; body } ->
      surround 2 1
        (group (surround 2 1 (doc_of_string "let tot") (binder_to_doc binder) (doc_of_string "=")))
        (term_to_doc head)
        (doc_of_string "in")
      ^/^ st_term_to_doc body

    | Tm_Abs { b; q; ascription=c; body } ->
      group (doc_of_string "fun" ^/^ parens (qual_to_doc q ^^ binder_to_doc b))
      ^/^ braced (st_term_to_doc body)

    | Tm_If { b; then_; else_ } ->
      prefix 2 1 (doc_of_string "if" ) (parens (term_to_doc b))
      ^/^ braced (st_term_to_doc then_)
      ^/^ doc_of_string "else"
      ^/^ braced (st_term_to_doc else_)

    | Tm_Match {sc; brs} ->
      surround 2 1 (doc_of_string "match") (parens (term_to_doc sc)) (doc_of_string "with")
      ^/^ braced (branches_to_doc brs)

    | Tm_IntroPure { p } ->
      prefix 2 1 (doc_of_string "introduce pure") (parens (term_to_doc p))

    | Tm_ElimExists { p } ->
      prefix 2 1 (doc_of_string "elim_exists") (parens (term_to_doc p))

    | Tm_IntroExists { p; witnesses } ->
      prefix 2 1 (doc_of_string "introduce") (parens (term_to_doc p))
      ^/^ doc_of_string "with" ^/^ separate_map (doc_of_string " ") term_to_doc witnesses

    | Tm_While { invariant; condition; body } ->
      prefix 2 1 (doc_of_string "while") (parens (group (st_term_to_doc condition)))
      ^/^ nest 2 (prefix 2 1 (doc_of_string "invariant") (term_to_doc invariant))
      ^/^ braced (st_term_to_doc body)

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      doc_of_string "par"
      ^/^ parens (angles (term_to_doc pre1) ^/^
                  parens (st_term_to_doc body1) ^/^
                  angles (term_to_doc post1))
      ^/^ parens (angles (term_to_doc pre2) ^/^
                  parens (st_term_to_doc body2) ^/^
                  angles (term_to_doc post2))

    | Tm_Rewrite { t1; t2 } ->
       doc_of_string "rewrite"
        ^/^ term_to_doc t1
        ^/^ doc_of_string "as"
        ^/^ term_to_doc t2

    | Tm_WithLocal { binder; initializer; body } ->
      doc_of_string "let mut" ^/^ binder_to_doc binder ^/^ doc_of_string "="
      ^/^ term_to_doc initializer ^/^ doc_of_string "in"
      ^/^ nest 2 (st_term_to_doc body)

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      doc_of_string "let mut" ^/^ binder_to_doc binder ^/^ doc_of_string "="
      ^/^ brackets (term_to_doc initializer ^/^ doc_of_string ";" ^/^ term_to_doc length)
      ^/^ doc_of_string "in"
      ^/^ nest 2 (st_term_to_doc body)

    | Tm_Admit { ctag; u; typ; post } ->
      doc_of_string (match ctag with
                      | STT -> "stt_admit"
                      | STT_Atomic -> "stt_atomic_admit"
                      | STT_Ghost -> "stt_ghost_admit")
      ^/^ angles (doc_of_string (universe_to_string 0 u))
      ^/^ term_to_doc typ
      ^/^ (match post with
           | None -> empty
           | Some post -> term_to_doc post)

    | Tm_ProofHintWithBinders { binders; hint_type; t } ->
      let with_prefix =
        match binders with
        | [] -> empty
        | _ -> doc_of_string "with" ^^ separate_map (doc_of_string " ") binder_to_doc binders ^^ doc_of_string "."
      in
      let names_to_doc = function
        | None -> empty
        | Some l -> brackets (separate_map (doc_of_string "; ") (fun n -> doc_of_string n) l)
      in
      let doc =
        match hint_type with
        | ASSERT { p } ->
           doc_of_string "assert" ^/^ term_to_doc p
        | UNFOLD { names; p } ->
            doc_of_string "unfold" ^/^ names_to_doc names ^/^ term_to_doc p
        | FOLD { names; p } ->
            doc_of_string "fold" ^/^ names_to_doc names ^/^ term_to_doc p
        | RENAME { pairs; goal } ->
            doc_of_string "rename each" ^/^
            separate_map (doc_of_string ", ") (fun (x, y) -> term_to_doc x ^/^ doc_of_string "as" ^/^ term_to_doc y) pairs
            ^/^ (match goal with
                 | None -> empty
                 | Some t -> doc_of_string "in" ^/^ term_to_doc t)
        | REWRITE { t1; t2 } ->
          doc_of_string "rewrite" ^/^ term_to_doc t1 ^/^ doc_of_string "as" ^/^ term_to_doc t2
      in
      with_prefix ^/^ doc ^^ semi ^/^ st_term_to_doc t

and branches_to_doc brs : T.Tac document =
  match brs with
  | [] -> empty
  | b::bs -> branch_to_doc b ^^ hardline ^^ branches_to_doc bs

and branch_to_doc (br:branch) : T.Tac document =
  let (pat, e) = br in
  braced (
    pattern_to_doc pat
    ^/^ doc_of_string "->"
    ^/^ nest 2 (st_term_to_doc e))

and pattern_to_doc (p:pattern) : T.Tac document =
  match p with
  | Pat_Cons fv pats ->
    doc_of_string (String.concat "." fv.fv_name)
    ^/^ separate_map (doc_of_string " ") (fun (p, _) -> pattern_to_doc p) pats
  | Pat_Constant c ->
    doc_of_string "<constant>"
  | Pat_Var x _ ->
    doc_of_string (T.unseal x)
  | Pat_Dot_Term None ->
    empty
  | Pat_Dot_Term (Some t) ->
    doc_of_string "(.??)" //%s)" (term_to_string t)

let pattern_to_string p = render (pattern_to_doc p)
let st_term_to_string t = render (st_term_to_doc t)

let tag_of_term (t:term) =
  match t.t with
  | Tm_Emp -> "Tm_Emp"
  | Tm_Pure _ -> "Tm_Pure"
  | Tm_Star _ _ -> "Tm_Star"
  | Tm_ExistsSL _ _ _ -> "Tm_ExistsSL"
  | Tm_ForallSL _ _ _ -> "Tm_ForallSL"
  | Tm_VProp -> "Tm_VProp"
  | Tm_Inames -> "Tm_Inames"
  | Tm_EmpInames -> "Tm_EmpInames"
  | Tm_Unknown -> "Tm_Unknown"
  | Tm_FStar _ -> "Tm_FStar"

let tag_of_st_term (t:st_term) =
  match t.term with
  | Tm_Return _ -> "Tm_Return"
  | Tm_Abs _ -> "Tm_Abs"
  | Tm_STApp _ -> "Tm_STApp"
  | Tm_Bind _ -> "Tm_Bind"
  | Tm_TotBind _ -> "Tm_TotBind"
  | Tm_If _ -> "Tm_If"
  | Tm_Match _ -> "Tm_Match"
  | Tm_IntroPure _ -> "Tm_IntroPure"
  | Tm_ElimExists _ -> "Tm_ElimExists"
  | Tm_IntroExists _ -> "Tm_IntroExists"
  | Tm_While _ -> "Tm_While"
  | Tm_Par _ -> "Tm_Par"
  | Tm_WithLocal _ -> "Tm_WithLocal"
  | Tm_WithLocalArray _ -> "Tm_WithLocalArray"
  | Tm_Rewrite _ -> "Tm_Rewrite"
  | Tm_Admit _ -> "Tm_Admit"
  | Tm_ProofHintWithBinders _ -> "Tm_ProofHintWithBinders"

let tag_of_comp (c:comp) : T.Tac string =
  match c with
  | C_Tot _ -> "Total"
  | C_ST _ -> "ST"
  | C_STAtomic i _ ->
    Printf.sprintf "Atomic %s" (term_to_string i)
  | C_STGhost i _ ->
    Printf.sprintf "Ghost %s" (term_to_string i)

let rec print_st_head (t:st_term)
  : Tot string (decreases t) =
  match t.term with
  | Tm_Abs _  -> "Abs"
  | Tm_Return p -> print_head p.term
  | Tm_Bind _ -> "Bind"
  | Tm_TotBind _ -> "TotBind"
  | Tm_If _ -> "If"
  | Tm_Match _ -> "Match"
  | Tm_While _ -> "While"
  | Tm_Admit _ -> "Admit"
  | Tm_Par _ -> "Par"
  | Tm_Rewrite _ -> "Rewrite"
  | Tm_WithLocal _ -> "WithLocal"
  | Tm_WithLocalArray _ -> "WithLocalArray"
  | Tm_STApp { head = p } -> print_head p
  | Tm_IntroPure _ -> "IntroPure"
  | Tm_IntroExists _ -> "IntroExists"
  | Tm_ElimExists _ -> "ElimExists"
  | Tm_ProofHintWithBinders _ -> "AssertWithBinders"
and print_head (t:term) =
  match t with
  // | Tm_FVar fv
  // | Tm_UInst fv _ -> String.concat "." fv.fv_name
  // | Tm_PureApp head _ _ -> print_head head
  | _ -> "<pure term>"


let rec print_skel (t:st_term) =
  match t.term with
  | Tm_Abs { body }  -> Printf.sprintf "(fun _ -> %s)" (print_skel body)
  | Tm_Return { term = p } -> print_head p
  | Tm_Bind { head=e1; body=e2 } -> Printf.sprintf "(Bind %s %s)" (print_skel e1) (print_skel e2)
  | Tm_TotBind { body=e2 } -> Printf.sprintf "(TotBind _ %s)" (print_skel e2)
  | Tm_If _ -> "If"
  | Tm_Match _ -> "Match"
  | Tm_While _ -> "While"
  | Tm_Admit _ -> "Admit"
  | Tm_Par _ -> "Par"
  | Tm_Rewrite _ -> "Rewrite"
  | Tm_WithLocal _ -> "WithLocal"
  | Tm_WithLocalArray _ -> "WithLocalArray"
  | Tm_STApp { head = p } -> print_head p
  | Tm_IntroPure _ -> "IntroPure"
  | Tm_IntroExists _ -> "IntroExists"
  | Tm_ElimExists _ -> "ElimExists"
  | Tm_ProofHintWithBinders _ -> "AssertWithBinders"

let decl_to_string (d:decl) : T.Tac string =
  match d.d with
  | FnDecl {id; isrec; body} ->
    "let " ^ (if isrec then "rec " else "") ^ fst (R.inspect_ident id) ^ " { " ^ st_term_to_string body ^ "}"
