module PulseSugar
open FStar.Ident
module A = FStar.Parser.AST
let rng = FStar.Compiler.Range.range
let dummyRange = FStar.Compiler.Range.dummyRange

type binder = A.aqual & ident & A.term

type binders = list binder

type vprop' =
  | VPropTerm of A.term
  | VPropStar of vprop & vprop
  | VPropExists {
      binders:binders;
      body:vprop
    }
and vprop = {
  v:vprop';
  vrange:rng
}

let as_vprop (v:vprop') (r:rng) = { v; vrange=r}

type st_comp_tag = 
  | ST
  | STAtomic
  | STGhost

type computation_type = {
     tag: st_comp_tag;
     precondition:vprop;
     return_name:ident;
     return_type:A.term;
     postcondition:vprop;
     opens:option A.term;
     range:rng
}

type mut_or_ref =
  | MUT | REF

type pat = 
  | PatVar of ident
  | PatConstructor {
      head:lident;
      args:list pat
    }

type hint_type =
  | ASSERT of vprop
  | UNFOLD of option (list lident) & vprop
  | FOLD of option (list lident) & vprop
  | RENAME of list (A.term & A.term) & option vprop
  | REWRITE of vprop & vprop

type array_init = {
  init : A.term;
  len : A.term;
}

type let_init =
  | Array_initializer of array_init
  | Default_initializer of A.term

type stmt' =
  | Open of lident
  
  | Expr { 
      e : A.term 
    }

  | Assignment {
      lhs:A.term;
      value:A.term;
    }

  | ArrayAssignment {
      arr:A.term;
      index:A.term;
      value:A.term;
    }

  | LetBinding {
      qualifier: option mut_or_ref;
      id:ident;
      typ:option A.term;
      init:option let_init
    }
      
  | Block { 
      stmt : stmt
    }
    
  | If {
      head:A.term;
      join_vprop:option vprop;
      then_:stmt;
      else_opt:option stmt;
    }

  | Match {
      head:A.term;
      returns_annot:option vprop;
      branches:list (A.pattern & stmt);
    }

  | While {
      guard: stmt;
      id: ident;
      invariant: vprop;
      body: stmt;
    }

  | Introduce {
      vprop:vprop;
      witnesses:list A.term
    }
      
  | Sequence {
      s1:stmt;
      s2:stmt;
    }

  | Parallel {
      p1:vprop;
      p2:vprop;
      q1:vprop;
      q2:vprop;
      b1:stmt;
      b2:stmt;
    }

  | Rewrite {
      p1:vprop;
      p2:vprop;
    }
    
  | ProofHintWithBinders {
      hint_type:hint_type;
      binders:binders;
    }

  | WithInvariants {
      names : list A.term;
      body  : stmt;
      returns_ : option vprop;
    }

and stmt = {
  s:stmt';
  range:rng
}

type decl =
  | FnDecl {
      id:ident;
      is_rec:bool;
      binders:binders;
      ascription:computation_type;
      measure:option A.term; // with binders in scope
      body:stmt;
      range:rng
    }

(* Convenience builders for use from OCaml/Menhir, since field names get mangled in OCaml *)
let mk_comp tag precondition return_name return_type postcondition opens range = 
  {
     tag;
     precondition;
     return_name;
     return_type;
     postcondition;
     opens;
     range
  }

let mk_vprop_exists binders body = VPropExists { binders; body }
let mk_expr e = Expr { e }
let mk_assignment id value = Assignment { lhs=id; value }
let mk_array_assignment arr index value = ArrayAssignment { arr; index; value }
let mk_let_binding qualifier id typ init = LetBinding { qualifier; id; typ; init }
let mk_block stmt = Block { stmt }
let mk_if head join_vprop then_ else_opt = If { head; join_vprop; then_; else_opt }
let mk_match head returns_annot branches = Match { head; returns_annot; branches }
let mk_while guard id invariant body = While { guard; id; invariant; body }
let mk_intro vprop witnesses = Introduce { vprop; witnesses }
let mk_sequence s1 s2 = Sequence { s1; s2 }
let mk_stmt s range = { s; range }
let mk_fn_decl id is_rec binders ascription measure body range = FnDecl { id; is_rec; binders; ascription; measure; body; range }
let mk_open lid = Open lid
let mk_par p1 p2 q1 q2 b1 b2 = Parallel { p1; p2; q1; q2; b1; b2 }
let mk_rewrite p1 p2 = Rewrite { p1; p2 }
let mk_proof_hint_with_binders ht bs =  ProofHintWithBinders { hint_type=ht; binders=bs }
let mk_with_invs names body returns_ = WithInvariants { names; body; returns_ }
