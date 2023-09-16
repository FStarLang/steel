module GhostTaskQueuePoolAlive
module L = FStar.List.Tot.Base
module P = FStar.Preorder


let smaller_status: P.preorder task_status =
fun (x y: task_status) -> 
    match x, y with
    | Done, Todo -> False
    | Done, Ongoing -> False
    | Ongoing, Todo -> False
    | _, _ -> True

let rec is_same_mono_list #a (x y: mono_list a) =
match x, y with
| [], [] -> True
| (tx, sx)::qx, (ty, sy)::qy ->
  tx == ty /\ smaller_status sx sy /\ is_same_mono_list qx qy
| _, _ -> False

let rec is_same_mono_same_length x y:
Lemma (is_same_mono_list x y ==> L.length x = L.length y)
= match x, y with
| _::qx, _::qy -> is_same_mono_same_length qx qy
| _ -> ()

let rec is_same_refl x:
Lemma (is_same_mono_list x x)
= match x with
| _::q -> is_same_refl q
| _ -> ()

let rec is_same_trans x y z:
Lemma (is_same_mono_list x y /\ is_same_mono_list y z ==> is_same_mono_list x z)
= match x, y, z with
| _::qx, _::qy, _::qz -> is_same_trans qx qy qz
| _ -> ()

let rec is_mono_suffix' #a (x y: mono_list a): prop
= if L.length x < L.length y then is_mono_suffix' x (L.tl y)
  else if L.length x = L.length y then is_same_mono_list x y
  else False

let is_mono_suffix_refl x:
Lemma (is_mono_suffix' x x)
= is_same_refl x

let rec is_mono_suffix_trans x y z:
Lemma (requires is_mono_suffix' x y /\ is_mono_suffix' y z)
(ensures is_mono_suffix' x z)
= if L.length y < L.length z then
    is_mono_suffix_trans x y (L.tl z)
  else (
    assert (L.length y == L.length z);
    if L.length x < L.length y then
        is_mono_suffix_trans x (L.tl y) (L.tl z)
    else is_same_trans x y z
  )

val is_mono_suffix (#a: Type): P.preorder (mono_list a)

let is_mono_suffix #a =
  introduce forall x. (is_mono_suffix' #a x x) with (is_mono_suffix_refl #a x);
  introduce forall x y z. (is_mono_suffix' #a x y /\ is_mono_suffix' y z
    ==> is_mono_suffix' x z) with (
  introduce (is_mono_suffix' #a x y /\ is_mono_suffix' y z)
    ==> is_mono_suffix' x z
    with _. (is_mono_suffix_trans x y z)
  );
  is_mono_suffix'

val task_in_queue (#a: Type) (x: a) (pos:nat) (l: mono_list a): prop

let rec task_in_queue #a (x: a) (pos:nat) (l: mono_list a) =
  if pos + 1 = L.length l then
    fst (L.hd l) == x
  else if pos + 1 < L.length l then
    task_in_queue x pos (L.tl l)
  else False

let rec task_in_queue_same_mono #a (t: a) (pos:nat) (x y: mono_list a):
Lemma (requires is_same_mono_list x y)
      (ensures task_in_queue t pos x ==> task_in_queue t pos y)
= is_same_mono_same_length x y;
  if pos + 1 < L.length x then
    task_in_queue_same_mono t pos (L.tl x) (L.tl y)
  else ()

// main reason why we want this preorder:
let rec task_in_queue_preorder #a 
    (t: a) (pos: nat) (x y: mono_list a):
Lemma (requires task_in_queue t pos x /\ is_mono_suffix x y)
      (ensures task_in_queue t pos y)
= if L.length x < L.length y then task_in_queue_preorder t pos x (L.tl y)
  else task_in_queue_same_mono t pos x y

// 1. enqueue: when spawning a new task
// get a certificate for task_in_queue
let enqueue_todo #a (l: mono_list a) (t: a)
(*
(r:mono_list a{ get_actual_queue r == t::get_actual_queue l
                /\ count_ongoing r == count_ongoing l } &
pos:nat{task_in_queue t pos r})
*)
= (| (t, Todo)::l, L.length l |)

let enqueue_preserves_order l t:
Lemma (is_mono_suffix l (enqueue_todo l t)._1)
= is_same_refl l

let rec count_ongoing #a (l: mono_list a): nat =
match l with
| [] -> 0
| (_, s)::q -> (if s = Ongoing then 1 else 0) + count_ongoing q

let get_actual_queue #a (l: mono_list a): list a =
    L.map fst (L.filter (fun t -> Todo? (snd t)) l)

// 2. pop: when a worker starts working on a task
// it updates the task to "ongoing"
let rec pop_todo_task #a (l: mono_list a{~(get_actual_queue l == [])})
: (t:a & r:mono_list a{ get_actual_queue l == t::get_actual_queue r
                /\ count_ongoing r == count_ongoing l + 1 }
  & pos:nat{task_in_queue t pos r})
= match l with
| (t, Todo)::q -> (| t, (t, Ongoing)::q, L.length l - 1 |)
| t::q -> let (| x, q', pos |) = pop_todo_task q in (| x, t::q', pos |)

let rec pop_preserves_order_aux l:
Lemma (requires ~(get_actual_queue l == []))
(ensures is_same_mono_list l (pop_todo_task l)._2)
= match l with
| (t, Todo)::q -> is_same_refl q
| t::q -> pop_preserves_order_aux q

let from_same_to_suffix x y:
Lemma (is_same_mono_list x y ==> is_mono_suffix x y)
= is_same_mono_same_length x y

let pop_preserves_order l:
Lemma (requires ~(get_actual_queue l == []))
      (ensures is_mono_suffix l (pop_todo_task l)._2)
= pop_preserves_order_aux l; from_same_to_suffix l (pop_todo_task l)._2

(** 3. concluding the task: when the worker is done **)
let task_in_queue_not_empty t pos l:
  Lemma (requires task_in_queue t pos l)
        (ensures L.length l >= 1)
= ()

let rec close_task #a
    (t: a)
    (pos: nat)
    (l: mono_list a{task_in_queue t pos l /\ L.length l >= 1}):
    (s:task_status{L.memP (t, s) l} & r:mono_list a{
        s == Ongoing ==> (
            get_actual_queue r == get_actual_queue l /\
            count_ongoing r == count_ongoing l - 1)})
= let (t', s)::q = l in
if pos + 1 = L.length l
  then (| s, (t', Done)::q |) // if s is not Ongoing, then we have too much permission
  else let (| s', q' |) = close_task t pos q in (| s', (t', s)::q' |)

let rec close_task_preserves_order_aux #a
    (t: a)
    (pos: nat)
    (l: mono_list a{task_in_queue t pos l}):
    Lemma (is_same_mono_list l (close_task t pos l)._2 )
= match l with
| (t', s)::q -> if pos + 1 = L.length l then is_mono_suffix_refl q
else let (| s', q' |) = close_task t pos q in close_task_preserves_order_aux t pos q

let close_task_preserves_order #a
    (t: a)
    (pos: nat)
    (l: mono_list a{task_in_queue t pos l}):
    Lemma (is_mono_suffix l (close_task t pos l)._2 )
= close_task_preserves_order_aux t pos l; from_same_to_suffix l (close_task t pos l)._2

(** Part 2: Instantiation as a ghost monotonic reference **)

module M = Pulse.Lib.GhostMonotonicHigherReference
open Pulse.Lib.Pervasives

#push-options "--print_universes"

//unfold
let ghost_mono_ref a = M.ref (mono_list a) is_mono_suffix

let pts_to_ghost_queue #a (r: ghost_mono_ref a) (l: mono_list a): vprop
= M.pts_to r full_perm l

//open Pulse.Lib.Pervasives

let pts_to_ghost_queue_half #a (r: ghost_mono_ref a) (l: mono_list a): vprop
= M.pts_to r one_half l

(*
assume val share_queue_general #a (r: ghost_mono_ref a) (l: mono_list a) f:
stt_ghost unit emp_inames (M.pts_to r f l)
  (fun () -> M.pts_to r (half_perm f) l ** M.pts_to r (half_perm f) l)
  *)

```pulse
ghost fn
share_queue (#a: Type) (r: ghost_mono_ref a) (l: mono_list a)
requires pts_to_ghost_queue r l
ensures pts_to_ghost_queue_half r l ** pts_to_ghost_queue_half r l
{
  unfold pts_to_ghost_queue r l;
  M.share #emp_inames r full_perm l;
  rewrite (M.pts_to r (half_perm full_perm) l)
    as pts_to_ghost_queue_half r l;
  rewrite (M.pts_to r (half_perm full_perm) l)
    as pts_to_ghost_queue_half r l;
  ()
}
```

```pulse
ghost fn gather_queue
(#a: Type) (r: ghost_mono_ref a) (l1: mono_list a) (l2: mono_list a)
requires pts_to_ghost_queue_half r l1 ** pts_to_ghost_queue_half r l2
ensures pts_to_ghost_queue r l1 ** pure (l1 == l2)
{
  unfold pts_to_ghost_queue_half r l1;
  unfold pts_to_ghost_queue_half r l2;
  M.gather #emp_inames r one_half one_half l1 l2;
  rewrite (M.pts_to r (sum_perm one_half one_half) l1)
    as (pts_to_ghost_queue r l1);
  ()
}
```



let alloc_ghost_queue (#a:Type)
  : stt_ghost (ghost_mono_ref a) emp_inames emp (fun r -> pts_to_ghost_queue r [])
= M.alloc is_mono_suffix []

let write_ghost_queue (#a:Type) (#v: mono_list a)
          (r:ghost_mono_ref a) (x: mono_list a)
  : stt_ghost unit emp_inames (pts_to_ghost_queue r v ** pure (squash (is_mono_suffix v x)))
               (fun v -> pts_to_ghost_queue r x)
= M.write r x

let task_in_queue_stable t pos:
Lemma (P.stable (task_in_queue t pos) is_mono_suffix)
= introduce forall x y. (task_in_queue t pos x /\ is_mono_suffix x y
==> task_in_queue t pos y) with
  (introduce (task_in_queue t pos x /\ is_mono_suffix x y)
  ==> task_in_queue t pos y with _. task_in_queue_preorder t pos x y)

// can witness that task is in queue
let witness (#a:Type) #t #pos
            (r:ghost_mono_ref a)
            (v:erased (mono_list a))
            (_:squash (task_in_queue t pos v))
  : //TODO: SteelAtomicUT
  stt_ghost (M.witnessed r (task_in_queue t pos)) emp_inames
                  (pts_to_ghost_queue r v)
                  (fun _ -> pts_to_ghost_queue r v)
= task_in_queue_stable t pos ; M.witness r (task_in_queue t pos) v _

let recall (#a:Type u#1) #t #pos
           (r:ghost_mono_ref a)
           (v:erased (mono_list a))
           (w:M.witnessed r (task_in_queue t pos))
  : //TODO: SteelAtomicU
 stt_ghost unit emp_inames
                 (pts_to_ghost_queue_half r v)
                 (fun _ -> pts_to_ghost_queue_half r v ** pure (task_in_queue t pos v))
  = M.recall (task_in_queue t pos) r v w

let recall_full (#a:Type u#1) #t #pos
           (r:ghost_mono_ref a)
           (v:erased (mono_list a))
           (w:M.witnessed r (task_in_queue t pos))
  : //TODO: SteelAtomicU
 stt_ghost unit emp_inames
                 (pts_to_ghost_queue r v)
                 (fun _ -> pts_to_ghost_queue r v ** pure (task_in_queue t pos v))
  = M.recall (task_in_queue t pos) r v w



(** Part 3: Associated permissions: Reasoning done here **)

module Lock = Pulse.Lib.SpinLock

let task_plus: Type u#1 = task_with_status task_elem

let mono_list_task_plus: Type u#1 = mono_list task_elem

let certificate (r:ghost_mono_ref task_elem) (t: task_elem) (pos: nat)
= M.witnessed r (task_in_queue t pos)

// can witness that task is in queue
let get_certificate (t: task_elem) (pos: nat)
            (r:ghost_mono_ref task_elem)
            (l:mono_list_task_plus)
            (_:squash (task_in_queue t pos l))
  : //TODO: SteelAtomicUT
  stt_ghost (certificate r t pos)
            emp_inames
                  (pts_to_ghost_queue r l)
                  (fun _ -> pts_to_ghost_queue r l)
= witness r l _

let pts_to_Some (t: task_elem & task_status) (f: perm): vprop
= (exists_ (fun v -> pts_to (t._1._2) #f v ** pure (Some? v)))

//let pts_to_Some (t: task_elem & task_status): vprop
//= (exists_ (fun v -> pts_to (t._1._2) #three_quart v ** pure (Some? v)))



let task_res_own (t: task_plus) (f: perm): vprop
= match t._2 with
| Todo -> pts_to (t._1._2) #f None // three_quarter
| Ongoing -> emp // in this case, the worker has the half permission
| Done -> pts_to_Some t f  //(exists_ (fun v -> pts_to (t._1._2) #three_quart v ** pure (Some? v)))

(*
let task_res_own (t: task_plus): vprop
= match t._2 with
| Todo -> pts_to (t._1._2) #three_quart None
| Ongoing -> emp // in this case, the worker has the half permission
| Done -> pts_to_Some t //(exists_ (fun v -> pts_to (t._1._2) #three_quart v ** pure (Some? v)))
*)



let rec tasks_res_own (l: mono_list_task_plus) (f: perm): vprop
=  match l with
  | [] -> emp
  | tl::ql -> task_res_own tl f ** tasks_res_own ql f
  
(*
let rec tasks_res_own (l: mono_list_task_plus): vprop
=  match l with
  | [] -> emp
  | tl::ql -> task_res_own tl ** tasks_res_own ql
*)

```pulse
ghost
fn fold_done_task (t: task_elem) (l:mono_list_task_plus) (f: perm)
  requires pts_to t._2 #f None ** tasks_res_own l f
  ensures tasks_res_own (enqueue_todo l t)._1 f
{
  rewrite (pts_to t._2 #f None) as (task_res_own (t, Todo) f);
  fold (task_res_own (t, Todo) f);
  rewrite (task_res_own (t, Todo) f ** tasks_res_own l f)
    as
  (tasks_res_own (enqueue_todo l t)._1 f);
  ()
}
```

(*
Old version:
let small_inv (r: ghost_mono_ref task_elem) (q: list task_elem) (c: int): vprop 
= exists_ (fun l -> pts_to_ghost_queue r l **
  tasks_res_own l **
  pure (count_ongoing l = c /\ get_actual_queue l == q)
)
*)

//let three_eight = half_perm three_quart

// TODO: Implement as a case distinction
```pulse
ghost fn
share_task_res_own_generic t (f1 f2: perm)
requires task_res_own t (sum_perm f1 f2)
ensures task_res_own t f1 ** task_res_own t f2
{
  admit()
}
```

```pulse
ghost fn
gather_task_res_own_generic t (f1 f2: perm)
requires task_res_own t f1 ** task_res_own t f2
ensures task_res_own t (sum_perm f1 f2)
{
  admit()
}
```



```pulse
ghost fn
share_task_res_own t (f: perm)
requires task_res_own t f
ensures task_res_own t (half_perm f) ** task_res_own t (half_perm f)
{
  rewrite task_res_own t f
    as (task_res_own t (sum_perm (half_perm f) (half_perm f)));
  share_task_res_own_generic t (half_perm f) (half_perm f);
  ()
}
```

// assuming because of universe polymorphism
assume val
stt_return #a (x:a): stt a emp (fun y -> pure (x == y))

// assuming because of universe polymorphism
assume val
stt_return_ghost #a (x:a): stt_ghost a emp_inames emp (fun y -> pure (x == y))

// Assuming recursion
assume val share_tasks_res_own_generic_cb (p: mono_list_task_plus) (f1: perm) (f2: perm):
stt_ghost unit emp_inames (tasks_res_own p (sum_perm f1 f2))
(fun () -> tasks_res_own p f1 ** tasks_res_own p f2)

```pulse
ghost fn
share_tasks_res_own_generic (l: mono_list_task_plus) (f1: perm) (f2: perm)
requires tasks_res_own l (sum_perm f1 f2)
ensures tasks_res_own l f1 ** tasks_res_own l f2
{
  if (L.length l = 0)
  {
    rewrite (tasks_res_own l (sum_perm f1 f2)) as emp;
    rewrite emp as (tasks_res_own l f1);
    rewrite emp as (tasks_res_own l f2);
    ()
  }
  else {
    let tl = stt_return_ghost (L.hd l);
    let ql = stt_return_ghost (L.tl l);
    rewrite (tasks_res_own l (sum_perm f1 f2))
      as (task_res_own tl (sum_perm f1 f2) ** tasks_res_own ql (sum_perm f1 f2));
    share_task_res_own_generic tl f1 f2;
    share_tasks_res_own_generic_cb ql f1 f2;
    rewrite (task_res_own tl f1 ** tasks_res_own ql f1)
      as (tasks_res_own l f1);
    rewrite (task_res_own tl f2 ** tasks_res_own ql f2)
      as (tasks_res_own l f2);
    ()
  }
}
```

```pulse
ghost fn
share_tasks_res_own_general (p: mono_list_task_plus) (f: perm)
requires tasks_res_own p f
ensures tasks_res_own p (half_perm f) ** tasks_res_own p (half_perm f)
{
  rewrite (tasks_res_own p f) as (tasks_res_own p (sum_perm (half_perm f) (half_perm f)));
  share_tasks_res_own_generic p (half_perm f) (half_perm f);
  ()
}
```

// assuming recursion
assume val gather_tasks_res_own_cb (l: mono_list_task_plus) (f1 f2: perm)
: stt_ghost unit emp_inames (tasks_res_own l f1 ** tasks_res_own l f2)
(fun () -> tasks_res_own l (sum_perm f1 f2))

```pulse
ghost fn gather_tasks_res_own (l: mono_list_task_plus) (f1 f2: perm)
requires tasks_res_own l f1 ** tasks_res_own l f2
ensures tasks_res_own l (sum_perm f1 f2)
{
  if (L.length l = 0) {
    rewrite (tasks_res_own l f1) as emp;
    rewrite (tasks_res_own l f2) as emp;
    rewrite emp as (tasks_res_own l (sum_perm f1 f2));
    ()
  }
  else
  {
    let tl = stt_return_ghost (L.hd l);
    let ql = stt_return_ghost (L.tl l);
    rewrite (tasks_res_own l f1) as (task_res_own tl f1 ** tasks_res_own ql f1);
    rewrite (tasks_res_own l f2) as (task_res_own tl f2 ** tasks_res_own ql f2);
    gather_task_res_own_generic tl f1 f2;
    gather_tasks_res_own_cb ql f1 f2;
    rewrite (task_res_own tl (sum_perm f1 f2) ** tasks_res_own ql (sum_perm f1 f2))
      as (tasks_res_own l (sum_perm f1 f2));
    ()
  }
}
```



```pulse
ghost fn
share_tasks_res_own (p: mono_list_task_plus)
requires tasks_res_own p three_quart
ensures tasks_res_own p one_half ** tasks_res_own p one_quart
{
  rewrite (tasks_res_own p three_quart)
    as (tasks_res_own p (sum_perm one_half one_quart));
  share_tasks_res_own_generic p one_half one_quart;
  ()
}
```





let deadline (r: ghost_mono_ref task_elem): vprop
= exists_ (fun f1 ->
  exists_ (fun f2 ->
  exists_ (fun l ->
    M.pts_to r f1 l ** tasks_res_own l f2
    ** pure (count_ongoing l = 0 /\ get_actual_queue l == [])
  )))

```pulse
ghost fn
duplicate_deadline' (r: ghost_mono_ref task_elem)
requires deadline r
ensures deadline r ** deadline r
{
  unfold deadline r;
  with f1 f2 l. assert (M.pts_to r f1 l ** tasks_res_own l f2
    ** pure (count_ongoing l = 0 /\ get_actual_queue l == []));
  M.share #emp_inames r f1 l;
  share_tasks_res_own_general l f2;
  fold deadline r;
  fold deadline r;
  ()
}
```

let duplicate_deadline = duplicate_deadline'

```pulse
ghost fn
obtain_deadline (r: ghost_mono_ref task_elem) (f: perm)
requires (exists l. pts_to_ghost_queue_half r l ** tasks_res_own l f **
      pure (count_ongoing l = 0 /\ get_actual_queue l == []))
  ensures deadline r
{
  with l. assert (pts_to_ghost_queue_half r l **
      pure (count_ongoing l = 0 /\ get_actual_queue l == []));
  unfold pts_to_ghost_queue_half r l;
  assert (M.pts_to r one_half l ** pure (count_ongoing l = 0 /\ get_actual_queue l == []));
  fold deadline r;
  ()
}
```

let small_inv (r: erased (ghost_mono_ref task_elem)) (q: list task_elem) (c: int): vprop 
= exists_ (fun l -> pts_to_ghost_queue_half r l **
  tasks_res_own l one_half **
  pure (count_ongoing l = c /\ get_actual_queue l == q)
  ** (if c = 0 && L.length q = 0 then deadline r
  else pts_to_ghost_queue_half r l ** tasks_res_own l one_quart)
)

```pulse
ghost fn
extract_deadline' (r: erased (ghost_mono_ref task_elem))
requires small_inv r [] 0
ensures small_inv r [] 0 ** deadline r
{
  unfold small_inv r [] 0;
  with l. assert (pts_to_ghost_queue_half r l);
  rewrite `@(if (0<:nat) = 0 && L.length ([] <: list task_elem) = 0 then deadline r
    else pts_to_ghost_queue_half r l ** tasks_res_own l one_quart)
  as deadline r;
  duplicate_deadline r;
  rewrite deadline r 
    as `@(if (0<:nat) = 0 && L.length ([] <: list task_elem) = 0 then deadline r
    else pts_to_ghost_queue_half r l ** tasks_res_own l one_quart);
  fold small_inv r [] 0;
  ()
}
```

let extract_deadline = extract_deadline'

```pulse
ghost
fn unfold_small_inv
(r: gmref) (q: list task_elem) (c: int)
requires small_inv r q c ** pure (c > 0 \/ L.length q > 0)
ensures exists l. (pts_to_ghost_queue r l
  ** tasks_res_own l three_quart
  ** pure (c = count_ongoing l /\ q == get_actual_queue l) 
)
{
  unfold small_inv r q c;
  with l. assert (pts_to_ghost_queue_half r l);
  rewrite `@(if c = 0 && L.length q = 0 then deadline r
  else pts_to_ghost_queue_half r l ** tasks_res_own l one_quart)
    as (pts_to_ghost_queue_half r l ** tasks_res_own l one_quart);
  //share_queue_general r l ;
  gather_queue r l l;
  gather_tasks_res_own l one_half one_quart;
  rewrite (tasks_res_own l (sum_perm one_half one_quart))
    as (tasks_res_own l three_quart);
  ()
}
```

```pulse
ghost
fn fold_small_inv
(r: gmref) (q: list task_elem) (c: int)
requires exists l. (pts_to_ghost_queue r l
  ** tasks_res_own l three_quart
  ** pure (c = count_ongoing l /\ q == get_actual_queue l)
  ** pure (c > 0 \/ L.length q > 0)
  )
ensures small_inv r q c
{
  with l. assert (pts_to_ghost_queue r l
  ** tasks_res_own l three_quart
  ** pure (c = count_ongoing l /\ q == get_actual_queue l)
  ** pure (c > 0 \/ L.length q > 0)
  );
  share_queue r l;
  rewrite (tasks_res_own l three_quart)
    as (tasks_res_own l (sum_perm one_half one_quart));
  share_tasks_res_own_generic l one_half one_quart;
  rewrite (pts_to_ghost_queue_half r l ** tasks_res_own l one_quart)
  as `@(if c = 0 && L.length q = 0 then deadline r
  else pts_to_ghost_queue_half r l ** tasks_res_own l one_quart);
  fold small_inv r q c;
  ()
}
```


#push-options "--print_universes --print_implicits"

assume val pts_to_perm (#a: _) (#p: _) (#v: _) (r: ref a)
  : stt_ghost unit emp_inames
      (pts_to r #p v)
      (fun _ -> pts_to r #p v ** pure (p `lesser_equal_perm` full_perm))
    
let hperm = (f:perm{lesser_equal_perm one_half f})

```pulse
ghost
fn derive_false_from_too_much_permission
(#a: Type) (r: ref a) (v1 v2: a) (f: hperm)
requires pts_to r #f v1 ** pts_to r #three_quart v2
ensures pts_to r #f v1 ** pts_to r #three_quart v2
  ** pure (~(r == r))
{
  gather #_ #emp_inames r #v1 #v2 #f #three_quart;
  pts_to_perm #_ #(sum_perm f three_quart) #v1 r;
  assert (pure False);
  share #_ #emp_inames r #v1 #(sum_perm f three_quart);
  rewrite (pts_to r #(half_perm (sum_perm f three_quart)) v1 **
    pts_to r #(half_perm (sum_perm f three_quart)) v1)
  as (pts_to r #f v1 ** pts_to r #three_quart v2);
  ()
}
```

```pulse
ghost
fn derive_status_ongoing (h: (task_elem & task_status)) (x: option h._1._1) (f: hperm)
  requires task_res_own h f ** (pts_to (h._1._2) #three_quart x)
  ensures task_res_own h f ** (pts_to (h._1._2) #three_quart x) ** pure (h._2 = Ongoing)
{
  if (snd h = Todo) {
    rewrite (task_res_own h f) as (pts_to (h._1._2) #f None);
    derive_false_from_too_much_permission h._1._2 None x f;
    assert (pure (h._2 = Ongoing));
    rewrite (pts_to (h._1._2) #f None) as (task_res_own h f);
    ()
  }
  else {
    if (snd h = Done) {
      rewrite (task_res_own h f) as (pts_to_Some h f);
      unfold (pts_to_Some h f);
      assert (exists_ (fun v -> pts_to (h._1._2) #f v ** pure (Some? v)));
      with v. assert (pts_to (h._1._2) #f v ** pure (Some? v));
      derive_false_from_too_much_permission h._1._2 v x f;
      fold (pts_to_Some h f);
      rewrite (pts_to_Some h f) as (task_res_own h f);
      ()
    }
    else {
      ()
    }
  }
}
```



// waiting to have recursion in Pulse
assume val prove_task_ongoing_aux_cb
  (t: task_elem)
  (pos: nat)
  (v: option t._1)
  (l: (l:mono_list_task_plus{task_in_queue t pos l /\ L.length l >= 1}))
  (f: hperm)
:
stt_ghost unit emp_inames
(tasks_res_own l f ** pts_to t._2 #three_quart v)
(fun () -> tasks_res_own l f  ** pts_to t._2 #three_quart v
  ** pure (count_ongoing l > 0))

```pulse
ghost
fn fold_tasks_res_own
  (h: (task_elem & task_status)) (q: mono_list_task_plus)
  (f: hperm)
requires task_res_own h f ** tasks_res_own q f
ensures tasks_res_own (h::q) f
{
  rewrite (task_res_own h f ** tasks_res_own q f) as (tasks_res_own (h::q) f);
  ()
}
```



```pulse
ghost
fn prove_task_ongoing_aux
  (t: task_elem)
  (pos: nat)
  (v: option t._1)
  (l: (l:mono_list_task_plus{task_in_queue t pos l /\ L.length l >= 1}))
  (f: hperm)
//stt_ghost unit emp_inames
requires tasks_res_own l f ** pts_to t._2 #three_quart v
ensures tasks_res_own l f ** pts_to t._2 #three_quart v ** pure (count_ongoing l > 0)
{
  let h = L.hd l;
  let q = L.tl l;

  unfold (tasks_res_own l f);
  rewrite `@(
  match l with
    | [] -> emp
    | tl::ql -> task_res_own tl f ** tasks_res_own ql f)
  as (task_res_own h f ** tasks_res_own q f);
  assert (pts_to t._2 #three_quart v);
  assert (task_res_own h f ** tasks_res_own q f);

  if (pos + 1 = L.length l)
  {
    rewrite (pts_to (t._2) #three_quart v) as (pts_to (h._1._2) #three_quart v);
    derive_status_ongoing h v f;
    assert (pure (count_ongoing l > 0));
    rewrite (pts_to (h._1._2) #three_quart v) as (pts_to (t._2) #three_quart v);
    assert (pts_to t._2 #three_quart v);
    fold_tasks_res_own h q f;
    fold tasks_res_own l f;
    ()
  }
  else {
    prove_task_ongoing_aux_cb t pos v q f;
    rewrite (task_res_own h f ** tasks_res_own q f) as
      `@(match l with
        | [] -> emp
        | tl::ql -> task_res_own tl f ** tasks_res_own ql f);
    fold (tasks_res_own l f);
   ()
 }
}
```

```pulse
ghost
fn prove_task_ongoing'
  (#t: task_elem)
  (#pos: nat)
  (#v: option t._1)
  (r: gmref)
  (q: list task_elem) (c: int)
  //(l: (l:mono_list task_elem{task_in_queue t pos l /\ L.length l >= 1})):
  (w:certificate r t pos)
//stt_ghost unit emp_inames
requires small_inv r q c ** pts_to t._2 #three_quart v
ensures small_inv r q c ** pts_to t._2 #three_quart v ** pure (c > 0)
{
  unfold small_inv r q c;
  with l. assert (pts_to_ghost_queue_half r l);
  let proof = recall #task_elem #t #pos r l w;
  assert (pure (task_in_queue t pos l));
  assert (pure (L.length l >= 1));
  prove_task_ongoing_aux t pos v l one_half;
  fold small_inv r q c;
  ()
}
```
//l

(*
  unfold is_active ct;
  with v. assert (pts_to ct._1._2 #three_quart v);
  prove_task_ongoing' #ct._1 #ct._2 #v r q c ct._3;
  assert (pure (c > 0));
  fold is_active ct;

  unfold_small_inv r q c;

*)

let convert_to_ghost_mono_ref (r: M.ref (mono_list task_elem) is_mono_suffix):
  gmref
  //ghost_mono_ref task_elem
  = r

// 0. init queue with task
```pulse
ghost fn init_ghost_queue' (t: task_elem)
requires pts_to t._2 #three_quart None
returns pair: erased (r: gmref & certificate r t 0)
ensures small_inv (reveal pair)._1 [t] 0
{
  let l: mono_list task_elem = [(t, Todo)];
  let r': M.ref (mono_list task_elem) is_mono_suffix = M.alloc #emp_inames #_ (is_mono_suffix) l;
  assert (M.pts_to r' full_perm l);
  let r: gmref = convert_to_ghost_mono_ref r';

  rewrite (M.pts_to r' full_perm l) as (pts_to_ghost_queue r l);
  let w: certificate r t 0 = get_certificate t 0 r l _;


  let pair': (r:gmref & certificate r t 0) = (| r, w |);
  let pair: erased (r:gmref & certificate r t 0) = hide pair';

  share_queue r l;
  assert (pure (count_ongoing l = 0 /\ get_actual_queue l == [t]));
  // now: create tasks_res_own
  //share pts_to t._2 #three_quart None
  //share pts_to t._2
  fold (task_res_own (t, Todo) three_quart);
  rewrite emp as (tasks_res_own [] three_quart);
  rewrite (task_res_own (t, Todo) three_quart ** tasks_res_own [] three_quart) as
    (tasks_res_own l three_quart);
  //fold (task_res_own t one_quart);
  share_tasks_res_own l;
  rewrite (pts_to_ghost_queue_half r l ** tasks_res_own l one_quart)
    as `@(if 1 = 0 && L.length [t] = 0 then deadline r
  else pts_to_ghost_queue_half r l ** tasks_res_own l one_quart);
  fold small_inv r [t] 0;
  rewrite (small_inv r [t] 0) as (small_inv (reveal pair)._1 [t] 0);
  pair
}
```

let init_ghost_queue = init_ghost_queue'



// 1: Enqueue
```pulse
ghost
fn spawn_task_ghost'
(r: gmref)
(q: list task_elem) (c: int) (t: task_elem)
(ct: current_task r)
  requires small_inv r q c ** pts_to t._2 #three_quart None ** is_active ct
  returns w: erased (pos:nat & certificate r t pos)
  ensures small_inv r (t::q) c ** is_active ct
{
  unfold is_active ct;
  with v. assert (pts_to ct._1._2 #three_quart v);
  prove_task_ongoing' #ct._1 #ct._2 #v r q c ct._3;
  assert (pure (c > 0));
  fold is_active ct;

  unfold_small_inv r q c;

  with vl. assert (pts_to_ghost_queue r vl);
  assert (tasks_res_own vl three_quart);
  assert (pure (count_ongoing vl = c /\ get_actual_queue vl == q));
  let p = enqueue_todo #task_elem vl t;
  let pos = p._2;
  assert (pure (task_in_queue t pos p._1));
  write_ghost_queue #task_elem #vl r p._1;
  assert (pts_to_ghost_queue r p._1);
  let w: certificate r t pos = get_certificate t pos r p._1 _;
  assert (tasks_res_own vl three_quart);
  fold_done_task t vl three_quart;
  assert (tasks_res_own (enqueue_todo vl t)._1 three_quart);
  assert (pts_to_ghost_queue r p._1);
  rewrite (tasks_res_own (enqueue_todo vl t)._1 three_quart)
    as (tasks_res_own p._1 three_quart);

  fold_small_inv r (t::q) c;
  //fold (small_inv r (t::q) c);
  let res = hide (| pos, w |);
  res
}
```

let spawn_task_ghost = spawn_task_ghost'

let rec vprop_equiv_test
  (l: mono_list_task_plus{~(get_actual_queue l == [])}) (f: perm)
: vprop_equiv (tasks_res_own l f)
  (pts_to (pop_todo_task l)._1._2 #f None
  ** tasks_res_own (pop_todo_task l)._2 f)
= match l with
| (t, Todo)::q ->
let p1: vprop_equiv (tasks_res_own l f) 
  (pts_to (pop_todo_task l)._1._2 #f None ** tasks_res_own q f) = vprop_equiv_refl _ in
let p2: vprop_equiv (tasks_res_own q f) (emp ** tasks_res_own q f) = 
  vprop_equiv_sym _ _ (vprop_equiv_unit _)
 in
let p3: vprop_equiv (emp ** tasks_res_own q f) (tasks_res_own (pop_todo_task l)._2 f) = vprop_equiv_refl _ in
let p4: vprop_equiv (tasks_res_own q f) (tasks_res_own (pop_todo_task l)._2 f) = vprop_equiv_trans _ _ _ p2 p3 in
let p5 = vprop_equiv_cong _ _ _ _ (vprop_equiv_refl (pts_to (pop_todo_task l)._1._2 #f None)) p4 in
vprop_equiv_trans _ _ _ p1 p5
| t::q -> 
let p1 = tasks_res_own l f in
let p2 = task_res_own t f in
let p3 = tasks_res_own q f in
let p4 = pts_to (pop_todo_task q)._1._2 #f None in
let p5 = tasks_res_own (pop_todo_task q)._2 f in
let p6 = tasks_res_own (pop_todo_task l)._2 f in
let e2: vprop_equiv p3 (p4 ** p5) = vprop_equiv_test q f in
let e3: vprop_equiv p1 (p2 ** (p4 ** p5)) = vprop_equiv_cong p2 p3 p2 (p4 ** p5) (vprop_equiv_refl _) e2 in
let e4: vprop_equiv (p2 ** (p4 ** p5)) ((p2 ** p4) ** p5) = vprop_equiv_sym _ _ (vprop_equiv_assoc _ _ _) in
let e5: vprop_equiv ((p2 ** p4) ** p5) ((p4 ** p2) ** p5) = vprop_equiv_cong (p2 ** p4) p5 (p4 ** p2) p5
  (vprop_equiv_comm _ _) (vprop_equiv_refl _) in
let e6: vprop_equiv ((p4 ** p2) ** p5) (p4 ** (p2 ** p5)) = vprop_equiv_assoc _ _ _ in
let e7: vprop_equiv (p2 ** (p4 ** p5)) (p4 ** (p2 ** p5)) = vprop_equiv_trans _ _ _ e4 (vprop_equiv_trans _ _ _ e5 e6)
in vprop_equiv_trans _ _ _ e3 e7

let get_permission_from_todo
  (l: mono_list_task_plus{~(get_actual_queue l == [])}) (f:perm)
: stt_ghost unit emp_inames
(tasks_res_own l f)
  (fun _ -> pts_to (pop_todo_task l)._1._2 #f None ** tasks_res_own (pop_todo_task l)._2 f)
= rewrite _ _ (vprop_equiv_test l f)

let mk_erased_pair #r #t (pos: nat) (w: certificate r t pos):
  erased (pos: nat & certificate r t pos)
= hide (|pos, w|)
  //returns pair:erased (pos:nat & certificate r t pos)

// 2: Pop
```pulse
ghost
fn pop_task_ghost'
(r: gmref)
(t: task_elem)
(q: list task_elem) (c: int)
//(ct: current_task r)
  requires small_inv r (t::q) c //** is_active ct
  returns pair:erased (pos:nat & certificate r t pos)
  ensures small_inv r q (c + 1) ** pts_to t._2 #three_quart None //** is_active ct
{
  //unfold is_active ct;
  //with v. assert (pts_to ct._1._2 #three_quart v);
  //prove_task_ongoing' #ct._1 #ct._2 #v r (t::q) c ct._3;
  //assert (pure (c > 0));
  //fold is_active ct;
  unfold_small_inv r (t::q) c;

  //unfold (small_inv r (t::q) c);
  with l. assert (pts_to_ghost_queue r l);
  assert (tasks_res_own l three_quart);
  assert (pure (count_ongoing l = c /\ get_actual_queue l == t::q));
  let p = pop_todo_task #task_elem l;
  let order_is_preserved = pop_preserves_order #task_elem l;
  write_ghost_queue #task_elem #l r p._2;
  assert (pts_to_ghost_queue r p._2);
  let certif: certificate r t p._3 = get_certificate t p._3 r p._2 ();
  assert (pts_to_ghost_queue r p._2);
  assert (pure (p._1 == t));
  get_permission_from_todo l three_quart;
  (*
requires exists l. (pts_to_ghost_queue r l
  ** tasks_res_own l three_quart
  ** pure (c = count_ongoing l /\ q == get_actual_queue l)
  ** pure (c > 0)
  )
  *)
  rewrite (tasks_res_own (pop_todo_task l)._2 three_quart)
    as (tasks_res_own p._2 three_quart);
  fold_small_inv r q (c + 1);
  //fold (small_inv r q (c + 1));
  rewrite (pts_to (pop_todo_task l)._1._2 #three_quart None)
    as (pts_to t._2 #three_quart None);
  let pair: erased (pos:nat & certificate r t pos) = mk_erased_pair p._3 certif;//(| p._3, certif |);
  pair
}
```

let pop_task_ghost = pop_task_ghost'

let rec close_task_bis #a
    (t: a)
    (pos: nat)
    (l: mono_list a{task_in_queue t pos l /\ L.length l >= 1}):
  mono_list a
= let (t', s)::q = l in
if pos + 1 = L.length l
  then (t', Done)::q // if s is not Ongoing, then we have too much permission
  else (t', s)::(close_task_bis t pos q)

let rec close_task_bis_preserves_order_aux #a
    (t: a)
    (pos: nat)
    (l: mono_list a{task_in_queue t pos l}):
    Lemma (is_same_mono_list l (close_task_bis t pos l) )
= match l with
| (t', s)::q -> if pos + 1 = L.length l then is_mono_suffix_refl q
else let q' = close_task_bis t pos q in close_task_bis_preserves_order_aux t pos q



let close_task_bis_preserves_order #a
    (t: a)
    (pos: nat)
    (l: mono_list a{task_in_queue t pos l}):
    Lemma (is_mono_suffix l (close_task_bis t pos l) )
= close_task_bis_preserves_order_aux t pos l; from_same_to_suffix l (close_task_bis t pos l)


```pulse
ghost
fn fold_task_done (h:(task_elem & task_status)) (f: perm)
  requires pts_to h._1._2 #f (Some x) ** pure (h._2 = Done)
  ensures task_res_own h f
{
  assert (pts_to h._1._2 #f (Some x) ** pure (Some? (Some x)));
  intro_exists (fun v -> pts_to h._1._2 #f v ** pure (Some? v)) (Some x);
  rewrite (exists_ (fun v -> pts_to h._1._2 #f v ** pure (Some? v))) as (pts_to_Some h f);
  rewrite (pts_to_Some h f) as (task_res_own h f);
  ()
}
```

// waiting to have recursion in Pulse
assume val put_back_permission_cb
  (t: task_elem)
  (pos: nat)
  (l: (l:mono_list_task_plus{task_in_queue t pos l /\ L.length l >= 1}))
  (x: t._1)
:
stt_ghost unit emp_inames
(tasks_res_own l three_quart ** pts_to t._2 #three_quart (Some x))
(fun () -> tasks_res_own (close_task_bis t pos l) three_quart ** pure (
 get_actual_queue (close_task_bis t pos l) == get_actual_queue l
  /\ count_ongoing (close_task_bis t pos l) + 1 == count_ongoing l))

```pulse
ghost
fn fold_tasks_res_own_bis
  (h: (task_elem & task_status)) 
  (h': (task_elem & task_status))
  (q: mono_list_task_plus)
 (pos: nat) (t: task_elem)
(l: (l:mono_list_task_plus{task_in_queue t pos l /\ b2t (L.length l >= 1)}))
requires task_res_own h' three_quart ** tasks_res_own q three_quart
  ** pure (t == h._1 /\ h == L.hd l /\ q == L.tl l /\ h' == (h._1, Done)
  /\ pos + 1 = L.length l
  )
  //** pure (t == h._1 /\ h == L.hd l /\ q == L.tl l)
//ensures tasks_res_own (h::q) f
ensures tasks_res_own (close_task_bis u#1 #task_elem t pos l) three_quart
{
  rewrite (task_res_own h' three_quart ** tasks_res_own q three_quart) as (tasks_res_own (h'::q) three_quart);
  rewrite (tasks_res_own (h'::q) three_quart)
    as (tasks_res_own (close_task_bis u#1 #task_elem t pos l) three_quart);
  ()
}
```




```pulse
ghost
fn put_back_permission
  (t: task_elem)
  (pos: nat)
  (l: (l:mono_list_task_plus{task_in_queue t pos l /\ L.length l >= 1}))
  (x: t._1)
requires tasks_res_own l three_quart ** pts_to t._2 #three_quart (Some x)
ensures tasks_res_own (close_task_bis t pos l) three_quart ** pure (
 get_actual_queue (close_task_bis t pos l) == get_actual_queue l
  /\ count_ongoing (close_task_bis t pos l) + 1 == count_ongoing l)
{
  let h = L.hd l;
  let q = L.tl l;

  unfold (tasks_res_own l three_quart);
  rewrite `@(
  match l with
    | [] -> emp
    | tl::ql -> task_res_own tl three_quart ** tasks_res_own ql three_quart)
  as (task_res_own h three_quart ** tasks_res_own q three_quart);
  assert (pts_to t._2 #three_quart (Some x));
  assert (task_res_own h three_quart ** tasks_res_own q three_quart);

  if (pos + 1 = L.length l)
  {
    assert (task_res_own h three_quart);
    rewrite (pts_to (t._2) #three_quart (Some x)) as (pts_to (h._1._2) #three_quart (Some x));
    derive_status_ongoing h (Some x) three_quart;
    assert (pure (snd h = Ongoing));
    assert (pts_to (h._1._2) #three_quart (Some x));

    unfold (task_res_own h three_quart); // not needed, can be dropped
    rewrite `@(match h._2 with
      | Todo -> pts_to (h._1._2) #three_quart None
      | Ongoing -> emp
      | Done -> (exists_ (fun v -> pts_to (h._1._2) #three_quart v ** pure (Some? v))))
    as (emp);

    let h' = (h._1, Done);
    rewrite (pts_to (h._1._2) #three_quart (Some x)) as (pts_to h'._1._2 #three_quart (Some x));
    fold_task_done h' three_quart;
    fold_tasks_res_own_bis h h' q pos t l;
    assert (tasks_res_own (close_task_bis u#1 #task_elem t pos l) three_quart);
    ()

  }
  else {
    put_back_permission_cb t pos q x;
    assert (tasks_res_own (close_task_bis t pos q) three_quart);
    assert (pure (get_actual_queue (close_task_bis t pos q) == get_actual_queue q));
    assert (pure (get_actual_queue (close_task_bis t pos l) == get_actual_queue l));
    assert (pure (count_ongoing (close_task_bis t pos q) + 1 == count_ongoing q));
    assert (pure (count_ongoing (close_task_bis t pos l) + 1 == count_ongoing l));

    rewrite (task_res_own h three_quart ** tasks_res_own (close_task_bis t pos q) three_quart) as
    `@(
    match (close_task_bis t pos l) with
      | [] -> emp
      | tl::ql -> task_res_own tl three_quart ** tasks_res_own ql three_quart);
    fold (tasks_res_own (close_task_bis t pos l) three_quart);
    ()
  }
}
```

let prove_task_ongoing = prove_task_ongoing'

```pulse
ghost
fn prove_ongoing_non_neg'
  (r:gmref)
  (q: list task_elem) (c: int)
requires small_inv r q c
ensures small_inv r q c ** pure (c >= 0)
{
  unfold small_inv r q c;
  fold small_inv r q c;
  ()
}
```

// TODO
let prove_ongoing_non_neg = prove_ongoing_non_neg'

#push-options "--print_implicits --print_universes"

// assume val assume_prop (p: prop): stt_ghost unit emp_inames emp (fun () -> pure p)

(*
```pulse
ghost fn imp_false (b: bool) (p: vprop)
  requires pure (b == false)
  ensures imp_vprop b p
{
  rewrite emp as (imp_vprop b p);
  ()
}
```

```pulse
ghost fn imp_true (b: bool) (p: vprop)
  requires pure (b == true) ** p
  ensures imp_vprop b p
{
  rewrite p as (imp_vprop b p);
  ()
}
```
*)


assume val drop (p: vprop): stt_ghost unit emp_inames p (fun () -> emp)

// 3: conclude the task
```pulse
ghost
fn conclude_task_ghost'
(#t: task_elem)
(#pos: nat)
(r: gmref)
(q: list task_elem) (c: int)
(x: t._1)
(w: certificate r t pos)
  requires small_inv r q c ** pts_to t._2 #three_quart (Some x)
  ensures small_inv r q (c - 1) //** imp_vprop (c = 1 && L.length q = 0) (deadline r)
{
  prove_task_ongoing' #t #pos #(Some x) r q c w;
  assert (pure (c > 0));
  unfold_small_inv r q c;
  //unfold (small_inv r q c);
  with l. assert (pts_to_ghost_queue r l);
  assert (tasks_res_own l three_quart);
  assert (pure (count_ongoing l = c /\ get_actual_queue l == q));
  let proof = recall_full #task_elem #t #pos r l w;
  let p = close_task_bis t pos l;
  let order_is_preserved = close_task_bis_preserves_order #task_elem t pos l;
  write_ghost_queue #task_elem #l r p;
  assert (pts_to_ghost_queue r p);

  put_back_permission t pos l x;
  assert (tasks_res_own (close_task_bis t pos l) three_quart);

  rewrite (tasks_res_own (close_task_bis u#1 #task_elem t pos (reveal u#1 #(mono_list u#1 task_elem) l)) three_quart)
    as (tasks_res_own p three_quart);

  assert (pts_to_ghost_queue r p);
  assert (pure (c - 1 = count_ongoing p /\ q == get_actual_queue p));

  let b: bool = stt_ghost_reveal _ (c - 1 = 0 && L.length q = 0);
  if (b)
  {
    share_queue r p;
    share_tasks_res_own p;
    obtain_deadline r one_quart;
    duplicate_deadline r;

    assert (pts_to_ghost_queue_half r p);
    //assert (tasks_res_own p one_half ** tasks_res_own p one_quart);
    rewrite (deadline r)
      as `@(if c - 1 = 0 && L.length q = 0 then deadline r
      else pts_to_ghost_queue_half r l ** tasks_res_own l one_quart);

    assert (pts_to_ghost_queue_half r p **
      tasks_res_own p one_half **
      pure (count_ongoing p = c - 1 /\ get_actual_queue p == q)
      ** `@(if c - 1 = 0 && L.length q = 0 then deadline r
      else pts_to_ghost_queue_half r p ** tasks_res_own p one_quart));
    fold (small_inv r q (c - 1));
    //imp_true (c = 1 && L.length q = 0) (deadline r);
    drop (deadline r);
    ()
  }
  else {
    fold_small_inv r q (c - 1);
    //imp_false (c = 1 && L.length q = 0) (deadline r);
    ()
  }
}
```

let conclude_task_ghost = conclude_task_ghost'

let recall_certificate (#t: task_elem) (#pos: nat)
           (r:ghost_mono_ref task_elem)
           (v: mono_list task_elem)
           (w:certificate r t pos)
= recall_full r v w


let pts_to_Some_fract (t:task_elem) (f: perm): vprop
= (exists_ (fun v -> pts_to t._2 #f v ** pure (Some? v)))

// assuming recursion
assume val get_Some_finished_aux_rec
  (t: task_elem) (pos: nat)
  (l: mono_list_task_plus)
  (f: perm)
: stt_ghost unit emp_inames
(tasks_res_own l f ** pure (task_in_queue t pos l) ** pure (count_ongoing l = 0 /\ get_actual_queue l == []))
(fun _ -> tasks_res_own l (half_perm f) ** pts_to_Some_fract t (half_perm f))

```pulse
ghost
fn get_Some_finished_aux
  (t: task_elem) (pos: nat)
  (l: mono_list_task_plus)
  (f: perm)
requires tasks_res_own l f ** pure (task_in_queue t pos l)
  ** pure (count_ongoing l = 0 /\ get_actual_queue l == [])
//returns x: t._1
//ensures tasks_res_own l f
ensures tasks_res_own l (half_perm f) ** pts_to_Some_fract t (half_perm f)
{
  let h = L.hd l;
  let q = L.tl l;

  rewrite (tasks_res_own l f) as (task_res_own h f ** tasks_res_own q f);

  if (pos + 1 = L.length l)
  {
    assert (task_res_own h f);
    assert (pure (fst h == t));
    assert (pure (snd h = Done));
    rewrite (task_res_own h f) as (pts_to_Some h f);
    unfold (pts_to_Some h f);
    with y. assert (pts_to h._1._2 #f y);
    share #_ #emp_inames h._1._2;
    //rewrite (pts_to_Some h (half_perm f)) as (pts_to_Some_fract t (half_perm f));
    //fold (pts_to_Some h (half_perm f));
    (*
fn fold_task_done (h:(task_elem & task_status)) (f: perm)
  requires pts_to h._1._2 #f (Some x) ** pure (h._2 = Done)
  ensures task_res_own h f
{
  *)
    with v. assert (pts_to h._1._2 #(half_perm f) v ** pure (Some? v));
    //let x = Some?.v y;
    assert (pure (Some (Some?.v v) == v));
    rewrite (pts_to h._1._2 #(half_perm f) v) as (pts_to h._1._2 #(half_perm f) (Some (Some?.v v)));
    rewrite (pts_to h._1._2 #(half_perm f) v) as (pts_to h._1._2 #(half_perm f) (Some (Some?.v v)));

    //assert pts_to h._1._2 #f (Some x) ** pure (h._2 = Done)
    fold_task_done h (half_perm f);
    //fold (pts_to_Some_fract t (half_perm f));
    //rewrite pts_to_Some h (half_perm f) as task_res_own h (half_perm f);
    //assert (pts_to_Some h (half_perm f) ** pts_to_Some h (half_perm f));
    //rewrite (pts_to_Some h (half_perm f)) as (task_res_own h (half_perm f));
    share_tasks_res_own_general q f;
    rewrite (task_res_own h (half_perm f) ** tasks_res_own q (half_perm f)) as (tasks_res_own l (half_perm f));
    drop (tasks_res_own q (half_perm f));
    //let x = Some?.v y;
    //x
    //unfold pts_to_Some h (half_perm f);
    assert (pure (h._1 == t));
    //with v. assert (pts_to h._1._2 #(half_perm f) v ** pure (Some? v));
    rewrite (pts_to h._1._2 #(half_perm f) v ** pure (Some? v))
      as (pts_to t._2 #(half_perm f) v ** pure (Some? v));
    //rewrite (pts_to_Some h (half_perm f)) as (pts_to_Some_fract t (half_perm f));
      //as (pts_to t._2 #(half_perm f) v ** pure (Some? v));
    //intro_exists (fun v -> pts_to t._2 #(half_perm f) v ** pure (Some? v)) v;
    fold pts_to_Some_fract t (half_perm f);
    ()
  }
  else {
    get_Some_finished_aux_rec t pos q f;
    share_task_res_own h f;
    rewrite (task_res_own h (half_perm f) ** tasks_res_own q (half_perm f))
      as (tasks_res_own l (half_perm f));
    drop (task_res_own h (half_perm f));
    ()
  }
}
```

let recall_certificate_fract (#t: task_elem) (#pos: nat)
           (r:ghost_mono_ref task_elem)
           (v: mono_list task_elem)
           (w:certificate r t pos)
           (f: perm):
 stt_ghost unit emp_inames
                 (M.pts_to r f v)
                 (fun _ -> M.pts_to r f v ** pure (task_in_queue t pos v))
  = M.recall (task_in_queue t pos) r v w



```pulse
ghost fn
proof_promise' (#t: task_elem) (#pos: nat)
  (r: gmref)
  (w:certificate r t pos)
requires deadline r
ensures deadline r ** (exists_ (fun f -> (exists_ (fun v ->
                          pts_to t._2 #f v ** pure (Some? v)))))
{
  unfold deadline r;
  with f1 f2 l. assert (M.pts_to r f1 l ** tasks_res_own l f2
    ** pure (count_ongoing l = 0 /\ get_actual_queue l == []));
  recall_certificate_fract r l w f1;
  get_Some_finished_aux t pos l f2;
  assert (tasks_res_own l (half_perm f2) ** pts_to_Some_fract t (half_perm f2));
  fold deadline r;
  unfold (pts_to_Some_fract t (half_perm f2));
  ()
}
```

let proof_promise = proof_promise'
