module Pulse.Typing.Metatheory.Renaming
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing
module RT = FStar.Reflection.Typing
module T = FStar.Tactics

assume
val tot_typing_renaming' 
        (#g:_) (#e:_) (#t:_) 
        (d:tot_typing g e t) (g':env) (r:renaming { renamed_envs g g' r})
   : tot_typing g' (rename_term r e) (rename_term r t)

let tot_typing_renaming #g #e #t d g' r = tot_typing_renaming' d g' r

let rename_arrow_cong (ty:term) (q:option qualifier) (c:comp) (r:renaming)
    : Lemma (rename_term r (tm_arrow (as_binder ty) q c) ==
             tm_arrow (as_binder (rename_term r ty)) q (rename_comp r c))
    = admit()

let rename_open_comp_cong (c:comp) (res:term) (r:renaming)
    : Lemma (rename_comp r (open_comp_with c res) ==
             open_comp_with (rename_comp r c) (rename_term r res))
    = calc (==) {
        rename_comp r (open_comp_with c res);
      (==) {}
        rename_comp r (subst_comp c [DT 0 res]);
      (==) {}
        subst_comp (subst_comp c [DT 0 res]) (as_subst r);
      (==) { _ by (T.tadmit()) } //commutation of substitutions
        subst_comp (subst_comp c (as_subst r)) [DT 0 (rename_term r res)];
      (==) {}
        subst_comp (rename_comp r c) [DT 0 (rename_term r res)];
      (==) {}
        open_comp_with (rename_comp r c) (rename_term r res);
      }

let st_typing_discriminator_t = #g:env -> #e:st_term -> #c:comp -> st_typing g e c -> bool

let st_typing_renaming_t (case: st_typing_discriminator_t) =
        (#g:_) -> (#e:st_term) -> (#c:comp) -> (d:st_typing g e c { case d }) ->
        (g':env) -> (r:renaming { renamed_envs g g' r}) ->
        (f: (#g:env -> #e:st_term -> #c:comp -> d':st_typing g e c ->
             g':env -> r:renaming { renamed_envs g g' r /\ d' << d  } ->
             st_typing g' (rename_st_term r e) (rename_comp r c))) ->
        st_typing g' (rename_st_term r e) (rename_comp r c)
    

let fresh_for (x:var) (g:env) = ~(x `Set.mem` dom g)

assume
val fresh2 (g g':env) : x:var { x `fresh_for` g /\ x `fresh_for` g' }

let extend_env (g:env) (x:var{ x `fresh_for` g}) (t:term) = push_binding g x ppname_default t

let renames (r:renaming) (x y:var) = 
    renaming_contains r x /\
    rename r x == y


assume
val extend_renaming (g g':env) (r:renaming { renamed_envs g g' r}) 
                    (x:var{ x `fresh_for` g })
                    (y:var { y `fresh_for` g' })
                    (ty:term)
    : r':renaming { 
        renames r' x y /\
        renamed_envs (extend_env g x ty) (extend_env g' y (rename_term r' ty)) r'
      }

// let test (g g':env) (r:renaming { renamed_envs g g' r}) 
//                     (x:var{ x `fresh_for` g })
//                     (y:var { y `fresh_for` g' })
//                     (ty:term)
//                     (r':renaming { 
//                             renames r' x y /\
//                             renamed_envs (extend_env g x ty) (extend_env g' y (rename_term r' ty)) r'
//                     })
//     = assert (forall t. rename_term r t == rename_term r' t);
//       assert false

// #push-options "--query_stats"
let st_typing_renaming_abs : st_typing_renaming_t T_Abs? =
    fun #g #e #c d g' r f ->
      let T_Abs g x q b u body c t_typing body_typing = d in
      let t_typing
        : tot_typing g' (rename_term r b.binder_ty) (tm_type u)
        = tot_typing_renaming' t_typing g' r
      in
      let y = fresh g' in
      let r' = extend_renaming g g' r x y b.binder_ty in
      let body_typing 
        = f body_typing (extend_env g' y (rename_term r' b.binder_ty)) r' in
      admit()
    
let st_typing_renaming_stapp : st_typing_renaming_t T_STApp? =
    fun #g #e #c d g' r f ->
      let T_STApp _ head ty q res arg head_typing arg_typing = d in    
      let head_typing = tot_typing_renaming head_typing g' r in
      let arg_typing = tot_typing_renaming arg_typing g' r in
      rename_arrow_cong ty q res r;
      rename_open_comp_cong res arg r;
      let d = T_STApp g' _ _ q (rename_comp r res) _ head_typing arg_typing in
      d
 
open FStar.Calc
let rec st_typing_renaming #g #e #c d g' r
  : Tot (st_typing g' (rename_st_term r e) (rename_comp r c))
        (decreases d)
  = match d with
    | T_Abs g x q b u body c t_typing body_typing ->
      st_typing_renaming_abs d g' r st_typing_renaming

    | T_STApp _ _ _ _ _ _ _ _ ->
      st_typing_renaming_stapp d g' r st_typing_renaming

    | _ -> admit()
      