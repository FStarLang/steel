use ocaml_interop::{
    impl_from_ocaml_record, impl_from_ocaml_variant, ocaml_export, FromOCaml, OCaml, OCamlInt64,
    OCamlList, OCamlRef, ToOCaml,
};
use proc_macro2::Span;
use syn::{
    punctuated::Punctuated, token::Brace, token::Colon, token::Comma, token::Eq, token::Let,
    token::Mut, token::Paren, token::Pub, token::RArrow, token::Ref, token::Semi, Block, Generics,
    Ident, ItemFn, Local, LocalInit, Pat as SynPat, PatType, Path, PathArguments, PathSegment,
    ReturnType, Signature, Type, TypePath, Visibility,
};

use std::fmt;

enum BinOp {
    Add,
    Sub,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match &self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
        };
        write!(f, "{}", s)
    }
}

struct ExprCall {
    call_fn: Box<Expr>,
    call_args: Vec<Expr>,
}

impl fmt::Display for ExprCall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let arg_s = self
            .call_args
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join(",");
        write!(f, "{}({})", self.call_fn.to_string(), arg_s)
    }
}

struct ExprBin {
    expr_bin_left: Box<Expr>,
    op: BinOp,
    expr_bin_right: Box<Expr>,
}

enum Expr {
    EBinOp(ExprBin),
    EPath(String),
    ECall(ExprCall),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Expr::EBinOp(e) => write!(f, "{} {} {}", e.expr_bin_left, e.op, e.expr_bin_right),
            Expr::EPath(s) => write!(f, "{}", s),
            Expr::ECall(e) => write!(f, "{}", e),
        }
    }
}

enum Typ {
    TName(String),
}

impl fmt::Display for Typ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Typ::TName(s) = self;
        write!(f, "{}", s)
    }
}

struct PatIdent {
    pat_name: String,
    by_ref: bool,
    is_mut: bool,
    pat_typ: Box<Typ>,
}

enum Pat {
    PIdent(PatIdent),
}

struct LocalStmt {
    local_stmt_pat: Pat,
    local_stmt_init: Option<Expr>,
}

impl fmt::Display for LocalStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Pat::PIdent(p) = &self.local_stmt_pat;
        write!(
            f,
            "let {} {} {}",
            if p.is_mut { "mut" } else { "" },
            p.pat_name,
            if let Some(e) = &self.local_stmt_init {
                format!("= {}", e)
            } else {
                "".to_string()
            }
        )
    }
}

enum Stmt {
    SLocal(LocalStmt),
    SExpr(Expr),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Stmt::SLocal(s) => write!(f, "{}", s),
            Stmt::SExpr(e) => write!(f, "{}", e),
        }
    }
}

enum FnArg {
    FnArgPat(Pat),
}

impl fmt::Display for FnArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let FnArg::FnArgPat(Pat::PIdent(p)) = &self;
        write!(
            f,
            "{}:{} {} {}",
            p.pat_name,
            if p.by_ref { "&" } else { "" },
            if p.is_mut { "mut" } else { "" },
            p.pat_typ
        )
    }
}

struct FnSig {
    fn_name: String,
    fn_args: Vec<FnArg>,
    fn_ret_t: Typ,
}

impl fmt::Display for FnSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "fn {}({}) -> {}",
            self.fn_name,
            self.fn_args
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(","),
            self.fn_ret_t
        )
    }
}
struct Fn {
    fn_sig: FnSig,
    fn_body: Vec<Stmt>,
}

impl fmt::Display for Fn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {{ {} }}",
            self.fn_sig,
            self.fn_body
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(";")
        )
    }
}

fn fn_to_string(f: &Fn) -> String {
    f.to_string()
}

impl_from_ocaml_variant! {
  BinOp {
      BinOp::Add,
      BinOp::Sub,
  }
}

impl_from_ocaml_variant! {
  Expr {
    Expr::EBinOp (payload:ExprBin),
    Expr::EPath (payload:String),
    Expr::ECall (payload:ExprCall),
  }
}

impl_from_ocaml_record! {
  ExprCall {
    call_fn : Expr,
    call_args : OCamlList<Expr>
  }
}

impl_from_ocaml_record! {
  ExprBin {
    expr_bin_left : Expr,
    op : BinOp,
    expr_bin_right : Expr,
  }
}

impl_from_ocaml_variant! {
  Typ {
    Typ::TName (payload:String),
  }
}

impl_from_ocaml_record! {
  PatIdent {
    pat_name : String,
    by_ref : bool,
    is_mut : bool,
    pat_typ : Typ,
  }
}

impl_from_ocaml_variant! {
  Pat {
    Pat::PIdent (payload:PatIdent),
  }
}

impl_from_ocaml_record! {
  LocalStmt {
    local_stmt_pat : Pat,
    local_stmt_init : Option<Expr>,
  }
}

impl_from_ocaml_variant! {
  Stmt {
    Stmt::SLocal (payload:LocalStmt),
    Stmt::SExpr (payload:Expr),
  }
}

impl_from_ocaml_variant! {
  FnArg {
    FnArg::FnArgPat (payload:Pat),
  }
}

impl_from_ocaml_record! {
  FnSig {
    fn_name : String,
    fn_args : OCamlList<FnArg>,
    fn_ret_t : Typ,
  }
}

impl_from_ocaml_record! {
  Fn {
    fn_sig : FnSig,
    fn_body : OCamlList<Stmt>,
  }
}

fn to_syn_path(s: String) -> syn::Path {
    let mut segs: Punctuated<syn::PathSegment, syn::token::PathSep> = Punctuated::new();
    segs.push(PathSegment {
        ident: Ident::new(&s, Span::call_site()),
        arguments: PathArguments::None,
    });
    Path {
        leading_colon: None,
        segments: segs,
    }
}

fn to_syn_expr(e: &Expr) -> syn::Expr {
    match e {
        Expr::EBinOp(e) => {
            let e1 = to_syn_expr(&e.expr_bin_left);
            let e2 = to_syn_expr(&e.expr_bin_right);
            syn::Expr::Binary(syn::ExprBinary {
                attrs: vec![],
                left: Box::new(e1),
                op: match e.op {
                    BinOp::Add => syn::BinOp::Add(syn::token::Plus {
                        spans: [Span::call_site()],
                    }),
                    BinOp::Sub => syn::BinOp::Sub(syn::token::Minus {
                        spans: [Span::call_site()],
                    }),
                },
                right: Box::new(e2),
            })
        }
        Expr::EPath(s) => {
            let path = to_syn_path(s.to_string());
            syn::Expr::Path(syn::ExprPath {
                attrs: vec![],
                qself: None,
                path,
            })
        }
        Expr::ECall(e) => {
            let mut args: Punctuated<syn::Expr, Comma> = Punctuated::new();
            e.call_args.iter().for_each(|a| args.push(to_syn_expr(a)));
            let func = Box::new(to_syn_expr(&e.call_fn));
            syn::Expr::Call(syn::ExprCall {
                attrs: vec![],
                func,
                paren_token: Paren::default(),
                args,
            })
        }
    }
}

fn to_pat_ident(p: &PatIdent) -> SynPat {
    SynPat::Ident(syn::PatIdent {
        attrs: vec![],
        by_ref: if p.by_ref {
            Some(Ref {
                span: Span::call_site(),
            })
        } else {
            None
        },
        mutability: if p.is_mut {
            Some(Mut {
                span: Span::call_site(),
            })
        } else {
            None
        },
        ident: Ident::new(&p.pat_name, Span::call_site()),
        subpat: None,
    })
}

fn to_syn_stmt(s: &Stmt) -> syn::Stmt {
    match s {
        Stmt::SLocal(s) => syn::Stmt::Local(Local {
            attrs: vec![],
            let_token: Let {
                span: Span::call_site(),
            },
            pat: {
                let Pat::PIdent(p) = &s.local_stmt_pat;
                to_pat_ident(&p)
            },
            init: s.local_stmt_init.as_ref().map(|e| {
                let e = to_syn_expr(&e);
                LocalInit {
                    eq_token: Eq {
                        spans: [Span::call_site()],
                    },
                    expr: Box::new(e),
                    diverge: None,
                }
            }),
            semi_token: Semi {
                spans: [Span::call_site()],
            },
        }),
        Stmt::SExpr(e) => {
            let e = to_syn_expr(&e);
            syn::Stmt::Expr(e, None)
        }
    }
}

fn to_syn_block(l: &Vec<Stmt>) -> Block {
    Block {
        brace_token: Brace::default(),
        stmts: l.iter().map(to_syn_stmt).collect(),
    }
}

fn to_syn_typ(t: &Typ) -> Type {
    let Typ::TName(s) = t;
    let path = to_syn_path(s.to_string());
    Type::Path(TypePath { qself: None, path })
}

fn to_syn_fn_arg(a: &FnArg) -> syn::FnArg {
    let FnArg::FnArgPat(Pat::PIdent(p)) = a;
    let t = to_syn_typ(&p.pat_typ);
    let pat: SynPat = to_pat_ident(p);
    syn::FnArg::Typed(PatType {
        attrs: vec![],
        pat: Box::new(pat),
        colon_token: Colon {
            spans: [Span::call_site()],
        },
        ty: Box::new(t),
    })
}

fn to_syn_fn_sig(s: &FnSig) -> Signature {
    let mut args: Punctuated<syn::FnArg, Comma> = Punctuated::new();
    s.fn_args.iter().for_each(|a| args.push(to_syn_fn_arg(a)));

    Signature {
        constness: None,
        asyncness: None,
        unsafety: None,
        abi: None,
        fn_token: syn::token::Fn {
            span: Span::call_site(),
        },
        ident: Ident::new(&s.fn_name, Span::call_site()),
        generics: Generics {
            lt_token: None,
            params: Punctuated::new(),
            gt_token: None,
            where_clause: None,
        },
        paren_token: Paren::default(),
        inputs: args,
        variadic: None,
        output: ReturnType::Type(
            RArrow {
                spans: [Span::call_site(), Span::call_site()],
            },
            Box::new(to_syn_typ(&s.fn_ret_t)),
        ),
    }
}

fn to_syn_fn(f: &Fn) -> ItemFn {
    ItemFn {
        attrs: vec![],
        vis: Visibility::Public(Pub {
            span: Span::call_site(),
        }),
        sig: to_syn_fn_sig(&f.fn_sig),
        block: Box::new(to_syn_block(&f.fn_body)),
    }
}

fn fn_to_syn_string(f: &Fn) -> String {
    let f: ItemFn = to_syn_fn(f);
    quote::quote!(#f).to_string()
}

ocaml_export! {
  fn rust_fn_to_string(cr, e:OCamlRef<Fn>) -> OCaml<String> {
    let e = cr.get(e);
    let e: Fn = e.to_rust ();
    fn_to_string(&e).to_owned ().to_ocaml(cr)
  }

  fn rust_expr_to_string(cr, e:OCamlRef<Expr>) -> OCaml<String> {
    let e = cr.get(e);
    let e: Expr = e.to_rust ();
    e.to_string().to_owned().to_ocaml(cr)
  }

  fn rust_fn_to_syn_string(cr, e:OCamlRef<Fn>) -> OCaml<String> {
    let e = cr.get(e);
    let e: Fn = e.to_rust ();
    fn_to_syn_string(&e).to_owned ().to_ocaml(cr)
  }

  fn rust_add_2(cr, x:OCamlRef<OCamlInt64>) -> OCaml<String> {
    let x = cr.get(x);
    let x: i64 = FromOCaml::from_ocaml(x);
    let z = x + 2;
    z.to_string().to_owned().to_ocaml(cr)
  }
}
