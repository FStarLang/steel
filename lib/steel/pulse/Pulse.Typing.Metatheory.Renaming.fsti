module Pulse.Typing.Metatheory.Renaming
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

let renaming = dom:list var & m:FStar.Map.t var var { 
    Set.as_set dom == Map.domain m /\
    (forall x y. {:pattern (Map.sel m x); (Map.sel m y)}
                Map.contains m x /\ Map.contains m y /\ x =!= y ==>
                Map.sel m x =!= Map.sel m y)
}

let renaming_contains (r:renaming) (x:var) = Map.contains (dsnd r) x

let var_as_term (x:var) =
  tm_var {nm_ppname=ppname_default;nm_index=x}

let as_subst (r:renaming) : subst = 
  let (| dom, m |) = r in
  List.Tot.map (fun x -> NT x (var_as_term (Map.sel m x))) dom

let rename (r:renaming) (x:var) : var = 
  Map.sel (dsnd r) x
 
let rename_term (r:renaming) (t:term) : term = 
  subst_term t (as_subst r)

let rename_comp (r:renaming) (c:comp) : comp = 
  subst_comp c (as_subst r)

let rename_st_term (r:renaming) (t:st_term) : st_term = 
  subst_st_term t (as_subst r)

let rename_bindings (bs:env_bindings) (r:renaming) =
   List.Tot.map (fun (x, t) -> (rename r x, rename_term r t)) bs 
   
let renamed_envs (g0 g1:env) (r:renaming) =
   fstar_env g0 == fstar_env g1 /\
   bindings g0 == rename_bindings (bindings g1) r

val tot_typing_renaming (#g:_) (#e:_) (#t:_) (d:tot_typing g e t)
                        (g':env) (r:renaming { renamed_envs g g' r})
  : tot_typing g' (rename_term r e) (rename_term r t)
  
val st_typing_renaming (#g:_) (#e:_) (#c:_) (d:st_typing g e c)
                       (g':env) (r:renaming { renamed_envs g g' r})
  : st_typing g' (rename_st_term r e) (rename_comp r c)
