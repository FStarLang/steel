module Pulse.Syntax.Base
module RTB = FStar.Reflection.Typing.Builtins
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2

let eq_univ (u1 u2:universe) : b:bool{b <==> u1 == u2} =
  let open FStar.Reflection.V2.TermEq in
  assume (faithful_univ u1);
  assume (faithful_univ u2);
  univ_eq_dec u1 u2

let rec eq_tm (t1 t2:term)
  : Tot (b:bool { b <==> (t1 == t2) }) (decreases t1)
  = match t1.t, t2.t with
    | Tm_VProp, Tm_VProp
    | Tm_Emp, Tm_Emp
    | Tm_Inames, Tm_Inames
    | Tm_EmpInames, Tm_EmpInames
    | Tm_Unknown, Tm_Unknown -> true
    | Tm_Star l1 r1, Tm_Star l2 r2 ->
      eq_tm l1 l2 &&
      eq_tm r1 r2
    | Tm_Inv p1, Tm_Inv p2 ->
      eq_tm p1 p2
    | Tm_Pure p1, Tm_Pure p2 ->
      eq_tm p1 p2
    | Tm_ExistsSL u1 t1 b1, Tm_ExistsSL u2 t2 b2
    | Tm_ForallSL u1 t1 b1, Tm_ForallSL u2 t2 b2 ->
      eq_univ u1 u2 &&
      eq_tm t1.binder_ty t2.binder_ty &&
      eq_tm b1 b2
    | Tm_FStar t1, Tm_FStar t2 ->
      let open FStar.Reflection.V2.TermEq in
      assume (faithful t1);
      assume (faithful t2);
      term_eq_dec t1 t2
    | _ -> false

let eq_st_comp (s1 s2:st_comp)  
  : b:bool { b <==> (s1 == s2) }
  = eq_univ s1.u s2.u &&
    eq_tm s1.res s2.res &&
    eq_tm s1.pre s2.pre &&
    eq_tm s1.post s2.post

let eq_comp (c1 c2:comp)
  : b:bool { b <==> (c1 == c2) }
  = match c1, c2 with
    | C_Tot t1, C_Tot t2 ->
      eq_tm t1 t2
    | C_ST s1, C_ST s2 ->
      eq_st_comp s1 s2
    | C_STAtomic i1 s1, C_STAtomic i2 s2
    | C_STGhost i1 s1, C_STGhost i2 s2 ->
      eq_tm i1 i2 &&
      eq_st_comp s1 s2
    | _ -> false

let rec eq_list (f: (x:'a -> y:'a -> b:bool { b <==> (x == y)})) (l m:list 'a)
  : b:bool { b <==> (l == m) }
  = match l, m with
    | [], [] -> true
    | h1::t1, h2::t2 ->
      f h1 h2 &&
      eq_list f t1 t2
    | _ -> false

let eq_opt (f: (x:'a -> y:'a -> b:bool { b <==> (x == y)})) (l m:option 'a)
  : b:bool { b <==> (l == m) }
  = match l, m with
    | None, None -> true
    | Some l, Some m -> f l m
    | _ -> false

let eq_tm_opt (t1 t2:option term)
  : b:bool { b <==> (t1 == t2) }
  = eq_opt eq_tm t1 t2

let eq_comp_opt (c1 c2:option comp)
  : b:bool { b <==> (c1 == c2) }
  = eq_opt eq_comp c1 c2

let rec eq_list_dec top1 top2
   (f: (x:'a -> y:'a{x << top1 /\ y << top2} -> b:bool { b <==> (x == y)}))
   (l : list 'a{l << top1})
   (m : list 'a{m << top2})
  : b:bool { b <==> (l == m) }
  = match l, m with
    | [], [] -> true
    | h1::t1, h2::t2 ->
      f h1 h2 &&
      eq_list_dec top1 top2 f t1 t2
    | _ -> false

let eq_binder (b0 b1:binder) : b:bool { b <==> (b0 == b1) } =
  eq_tm b0.binder_ty b1.binder_ty

let eq_tm_list (t1 t2:list term) = eq_list eq_tm t1 t2

// wire to Reflection.TermEq
assume val fstar_const_eq : c1:R.vconst -> c2:R.vconst -> b:bool{b <==> (c1==c2)}

let rec sealed_list_eq #a (l1 l2 : list (Sealed.sealed a))
  : Lemma ((length l1 = length l2) ==> (l1 == l2))
  = match l1, l2 with
    | [], [] -> ()
    | h1::t1, h2::t2 ->
      Sealed.sealed_singl h1 h2;
      sealed_list_eq t1 t2
    | _ -> ()

let rec eq_pattern (p1 p2 : pattern) : b:bool{ b <==> (p1 == p2) } =
  match p1, p2 with
  | Pat_Cons f1 vs1,
    Pat_Cons f2 vs2 ->
    f1.fv_name = f2.fv_name &&
    eq_list_dec p1 p2 eq_sub_pat vs1 vs2

  | Pat_Constant c1, Pat_Constant c2 ->
    fstar_const_eq c1 c2

  | Pat_Var _, Pat_Var _ -> true
  
  | Pat_Dot_Term to1, Pat_Dot_Term to2 -> eq_opt eq_tm to1 to2

  | _ -> false

and eq_sub_pat (pb1 pb2 : pattern & bool) : b:bool{b <==> pb1 == pb2} =
  let (p1, b1) = pb1 in
  let (p2, b2) = pb2 in
  eq_pattern p1 p2 && b1 = b2

let rec eq_st_term (t1 t2:st_term) 
  : b:bool { b <==> (t1 == t2) }
  = match t1.term, t2.term with
    | Tm_Return {ctag=c1; insert_eq=b1; term=t1}, 
      Tm_Return {ctag=c2; insert_eq=b2; term=t2} ->
      c1 = c2 &&
      b1 = b2 &&
      eq_tm t1 t2

    | Tm_Abs { b=b1; q=o1; ascription=c1; body=t1 },
      Tm_Abs { b=b2; q=o2; ascription=c2; body=t2 } ->
      eq_tm b1.binder_ty b2.binder_ty &&
      o1=o2 &&
      eq_comp c1 c2 &&
      eq_st_term t1 t2
  
    | Tm_STApp { head=h1; arg_qual=o1; arg=t1},
      Tm_STApp { head=h2; arg_qual=o2; arg=t2} ->
      eq_tm h1 h2 &&
      o1=o2 &&
      eq_tm t1 t2

    | Tm_Bind { binder=b1; head=t1; body=k1 },
      Tm_Bind { binder=b2; head=t2; body=k2 } ->
      eq_tm b1.binder_ty b2.binder_ty &&
      eq_st_term t1 t2 &&
      eq_st_term k1 k2

    | Tm_TotBind { binder=b1; head=t1; body=k1 },
      Tm_TotBind { binder=b2; head=t2; body=k2 } ->
      eq_tm b1.binder_ty b2.binder_ty &&
      eq_tm t1 t2 &&
      eq_st_term k1 k2
      
    | Tm_IntroPure { p=p1 }, Tm_IntroPure { p=p2 } ->
      eq_tm p1 p2

    | Tm_IntroExists { p=p1; witnesses=l1 },
      Tm_IntroExists { p=p2; witnesses=l2 } ->
      eq_tm p1 p2 &&
      eq_tm_list l1 l2

    | Tm_ElimExists {p=p1},
      Tm_ElimExists {p=p2} ->
      eq_tm p1 p2

    | Tm_If { b=g1; then_=ethen1; else_=eelse1; post=p1},
      Tm_If { b=g2; then_=ethen2; else_=eelse2; post=p2} ->
      eq_tm g1 g2 &&
      eq_st_term ethen1 ethen2 &&
      eq_st_term eelse1 eelse2 &&
      eq_tm_opt p1 p2
    
    | Tm_Match {sc=sc1; returns_=r1; brs=br1},
      Tm_Match {sc=sc2; returns_=r2; brs=br2} ->
      eq_tm sc1 sc2 &&
      eq_tm_opt r1 r2 &&
      eq_list_dec t1 t2 eq_branch br1 br2

    | Tm_While { invariant=inv1; condition=cond1; body=body1 },
      Tm_While { invariant=inv2; condition=cond2; body=body2 } ->
      eq_tm inv1 inv2 &&
      eq_st_term cond1 cond2 &&
      eq_st_term body1 body2

    | Tm_Par {pre1=preL1; body1=eL1; post1=postL1; pre2=preR1; body2=eR1; post2=postR1 },
      Tm_Par {pre1=preL2; body1=eL2; post1=postL2; pre2=preR2; body2=eR2; post2=postR2 } ->
      eq_tm preL1 preL2 &&
      eq_st_term eL1 eL2 &&
      eq_tm postL1 postL2 &&
      eq_tm preR1 preR2 &&
      eq_st_term eR1 eR2 &&
      eq_tm postR1 postR2

    | Tm_WithLocal { binder=x1; initializer=e1; body=b1 },
      Tm_WithLocal { binder=x2; initializer=e2; body=b2 } ->
      eq_tm x1.binder_ty x2.binder_ty &&
      eq_tm e1 e2 &&
      eq_st_term b1 b2

    | Tm_Rewrite { t1=l1; t2=r1 },
      Tm_Rewrite { t1=l2; t2=r2 } ->
      eq_tm l1 l2 &&
      eq_tm r1 r2

    | Tm_Admit { ctag=c1; u=u1; typ=t1; post=post1 }, 
      Tm_Admit { ctag=c2; u=u2; typ=t2; post=post2 } ->
      c1 = c2 &&
      eq_univ u1 u2 &&
      eq_tm t1 t2 &&
      eq_tm_opt post1 post2
      
    | Tm_ProofHintWithBinders { hint_type=ht1; binders=bs1; t=t1; v=v1 },
      Tm_ProofHintWithBinders { hint_type=ht2; binders=bs2; t=t2; v=v2 } ->
      ht1 = ht2 &&
      eq_list eq_binder bs1 bs2 &&
      eq_tm v1 v2 &&
      eq_st_term t1 t2

    | Tm_WithInv {name=name1; returns_inv=r1; body=body1},
      Tm_WithInv {name=name2; returns_inv=r2; body=body2} ->
      eq_tm name1 name2 &&
      eq_tm_opt r1 r2 &&
      eq_st_term body1 body2

    | _ -> false

and eq_branch (b1 b2 : pattern & st_term)
  : b:bool{b <==> (b1 == b2)}
  = let (p1, e1) = b1 in
    let (p2, e2) = b2 in
    eq_pattern p1 p2 && eq_st_term e1 e2
