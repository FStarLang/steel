module GhostTaskQueue
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

let is_mono_suffix #a =
  introduce forall x. (is_mono_suffix' #a x x) with (is_mono_suffix_refl #a x);
  introduce forall x y z. (is_mono_suffix' #a x y /\ is_mono_suffix' y z
    ==> is_mono_suffix' x z) with (
  introduce (is_mono_suffix' #a x y /\ is_mono_suffix' y z)
    ==> is_mono_suffix' x z
    with _. (is_mono_suffix_trans x y z)
  );
  is_mono_suffix'

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

// 2. pop: when a worker starts working on a task
// it updates the task to "ongoing"
let rec pop_todo_task #a (l: mono_list a{~(get_actual_queue l == [])})
: (t:a & r:mono_list a{ get_actual_queue l == t::get_actual_queue r
                /\ count_ongoing r == count_ongoing l + 1 })
= match l with
| (t, Todo)::q -> (| t, (t, Ongoing)::q |)
| t::q -> let (| x, q' |) = pop_todo_task q in (| x, t::q' |)

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

let ghost_mono_ref a = M.ref (mono_list a) is_mono_suffix

let pts_to_ghost_queue #a (r: ghost_mono_ref a) (l: mono_list a): vprop
= M.pts_to r full_perm l

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
            (l:erased mono_list_task_plus)
            (_:squash (task_in_queue t pos l))
  : //TODO: SteelAtomicUT
  stt_ghost (certificate r t pos)
            emp_inames
                  (pts_to_ghost_queue r l)
                  (fun _ -> pts_to_ghost_queue r l)
= witness r l _

let pts_to_Some (t: task_elem & task_status): vprop
= (exists_ (fun v -> pts_to (t._1._2) #three_quart v ** pure (Some? v)))

let task_res_own (t: task_plus): vprop
= match t._2 with
| Todo -> pts_to (t._1._2) #three_quart None
| Ongoing -> emp // in this case, the worker has the half permission
| Done -> pts_to_Some t  //(exists_ (fun v -> pts_to (t._1._2) #three_quart v ** pure (Some? v)))

  
let rec tasks_res_own (l: mono_list_task_plus): vprop
=  match l with
  | [] -> emp
  | tl::ql -> task_res_own tl ** tasks_res_own ql

```pulse
ghost
fn fold_done_task (t: task_elem) (l:mono_list_task_plus)
  requires pts_to t._2 #three_quart None ** tasks_res_own l
  ensures tasks_res_own (enqueue_todo l t)._1
{
  rewrite (pts_to t._2 #three_quart None) as (task_res_own (t, Todo));
  fold (task_res_own (t, Todo));
  rewrite (task_res_own (t, Todo) ** tasks_res_own l)
    as
  (tasks_res_own (enqueue_todo l t)._1);
  ()
}
```

let small_inv (r: ghost_mono_ref task_elem) (q: list task_elem) (c: int): vprop 
= exists_ (fun l -> pts_to_ghost_queue r l **
  tasks_res_own l **
  pure (count_ongoing l = c /\ get_actual_queue l == q)
)

#push-options "--print_universes --print_implicits"

// 1: Enqueue
```pulse
ghost
fn spawn_task_ghost'
(r: ghost_mono_ref task_elem)
(q: list task_elem) (c: int) (t: task_elem)
  requires small_inv r q c ** pts_to t._2 #three_quart None 
  returns w: erased (pos:nat & certificate r t pos)
  ensures small_inv r (t::q) c
{
  unfold (small_inv r q c);
  with vl. assert (pts_to_ghost_queue r vl);
  assert (tasks_res_own vl);
  assert (pure (count_ongoing vl = c /\ get_actual_queue vl == q));
  let p = enqueue_todo #task_elem vl t;
  let pos = p._2;
  assert (pure (task_in_queue t pos p._1));
  write_ghost_queue #task_elem #vl r p._1;
  assert (pts_to_ghost_queue r p._1);
  let w: certificate r t pos = get_certificate t pos r p._1 _;
  fold_done_task t vl;
  fold (small_inv r (t::q) c);
  let res = hide (| pos, w |);
  res
}
```

let spawn_task_ghost = spawn_task_ghost'

let rec vprop_equiv_test
  (l: mono_list_task_plus{~(get_actual_queue l == [])})
: vprop_equiv (tasks_res_own l)
  (pts_to (pop_todo_task l)._1._2 #three_quart None
  ** tasks_res_own (pop_todo_task l)._2)
= match l with
| (t, Todo)::q ->
let p1: vprop_equiv (tasks_res_own l) 
  (pts_to (pop_todo_task l)._1._2 #three_quart None ** tasks_res_own q) = vprop_equiv_refl _ in
let p2: vprop_equiv (tasks_res_own q) (emp ** tasks_res_own q) = 
  vprop_equiv_sym _ _ (vprop_equiv_unit _)
 in
let p3: vprop_equiv (emp ** tasks_res_own q) (tasks_res_own (pop_todo_task l)._2) = vprop_equiv_refl _ in
let p4: vprop_equiv (tasks_res_own q) (tasks_res_own (pop_todo_task l)._2) = vprop_equiv_trans _ _ _ p2 p3 in
let p5 = vprop_equiv_cong _ _ _ _ (vprop_equiv_refl (pts_to (pop_todo_task l)._1._2 #three_quart None)) p4 in
vprop_equiv_trans _ _ _ p1 p5
| t::q -> 
let p1 = tasks_res_own l in
let p2 = task_res_own t in
let p3 = tasks_res_own q in
let p4 = pts_to (pop_todo_task q)._1._2 #three_quart None in
let p5 = tasks_res_own (pop_todo_task q)._2 in
let p6 = tasks_res_own (pop_todo_task l)._2 in
let e2: vprop_equiv p3 (p4 ** p5) = vprop_equiv_test q in
let e3: vprop_equiv p1 (p2 ** (p4 ** p5)) = vprop_equiv_cong p2 p3 p2 (p4 ** p5) (vprop_equiv_refl _) e2 in
let e4: vprop_equiv (p2 ** (p4 ** p5)) ((p2 ** p4) ** p5) = vprop_equiv_sym _ _ (vprop_equiv_assoc _ _ _) in
let e5: vprop_equiv ((p2 ** p4) ** p5) ((p4 ** p2) ** p5) = vprop_equiv_cong (p2 ** p4) p5 (p4 ** p2) p5
  (vprop_equiv_comm _ _) (vprop_equiv_refl _) in
let e6: vprop_equiv ((p4 ** p2) ** p5) (p4 ** (p2 ** p5)) = vprop_equiv_assoc _ _ _ in
let e7: vprop_equiv (p2 ** (p4 ** p5)) (p4 ** (p2 ** p5)) = vprop_equiv_trans _ _ _ e4 (vprop_equiv_trans _ _ _ e5 e6)
in vprop_equiv_trans _ _ _ e3 e7

let get_permission_from_todo
  (l: mono_list_task_plus{~(get_actual_queue l == [])})
: stt_ghost unit emp_inames
(tasks_res_own l)
  (fun _ -> pts_to (pop_todo_task l)._1._2 #three_quart None ** tasks_res_own (pop_todo_task l)._2)
= rewrite _ _ (vprop_equiv_test l)

// 2: Pop
```pulse
ghost
fn pop_task_ghost'
(r: ghost_mono_ref task_elem)
(t: task_elem)
(q: list task_elem) (c: int)
  requires small_inv r (t::q) c
  ensures small_inv r q (c + 1) ** pts_to t._2 #three_quart None 
{
  unfold (small_inv r (t::q) c);
  with l. assert (pts_to_ghost_queue r l);
  assert (tasks_res_own l);
  assert (pure (count_ongoing l = c /\ get_actual_queue l == t::q));
  let p = pop_todo_task #task_elem l;
  let order_is_preserved = pop_preserves_order #task_elem l;
  write_ghost_queue #task_elem #l r p._2;
  assert (pts_to_ghost_queue r p._2);
  assert (pure (p._1 == t));
  get_permission_from_todo l;
  fold (small_inv r q (c + 1));
  rewrite (pts_to (pop_todo_task l)._1._2 #three_quart None)
    as (pts_to t._2 #three_quart None);
  ()
}
```

let pop_task_ghost = pop_task_ghost'

assume val pts_to_perm (#a: _) (#p: _) (#v: _) (r: ref a)
  : stt_ghost unit emp_inames
      (pts_to r #p v)
      (fun _ -> pts_to r #p v ** pure (p `lesser_equal_perm` full_perm))
    
assume val gather_pt
  (#a:Type0) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
: stt_ghost unit emp_inames
    (pts_to r #p0 v0 ** pts_to r #p1 v1)
    (fun _ -> pts_to r #(sum_perm p0 p1) v0 ** pure (v0 == v1))

assume val share_pt
  (#a:Type0) (#p:perm) (#v:erased a) (r:ref a)
  : stt_ghost unit emp_inames
    (pts_to r #p v)
    (fun _ -> pts_to r #(half_perm p) v ** pts_to r #(half_perm p) v)

```pulse
ghost
fn derive_false_from_too_much_permission
(#a: Type) (r: ref a) (v1 v2: a)
requires pts_to r #three_quart v1 ** pts_to r #three_quart v2
ensures pts_to r #three_quart v1 ** pts_to r #three_quart v2
  ** pure (~(r == r))
{
  gather_pt #a #three_quart #three_quart #v1 #v2 r;
  pts_to_perm #_ #(sum_perm three_quart three_quart) #v1 r;
  assert (pure False);
  share_pt #a #(sum_perm three_quart three_quart) #v1 r;
  rewrite (pts_to r #(half_perm (sum_perm three_quart three_quart)) v1 **
    pts_to r #(half_perm (sum_perm three_quart three_quart)) v1)
  as (pts_to r #three_quart v1 ** pts_to r #three_quart v2);
  ()
}
```

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
fn derive_status_ongoing (h: (task_elem & task_status)) (x: option h._1._1)
  requires task_res_own h ** (pts_to (h._1._2) #three_quart x)
  ensures task_res_own h ** (pts_to (h._1._2) #three_quart x) ** pure (h._2 = Ongoing)
{
  if (snd h = Todo) {
    rewrite (task_res_own h) as (pts_to (h._1._2) #three_quart None);
    derive_false_from_too_much_permission h._1._2 None x;
    assert (pure (h._2 = Ongoing));
    rewrite (pts_to (h._1._2) #three_quart None) as (task_res_own h);
    ()
  }
  else {
    if (snd h = Done) {
      rewrite (task_res_own h) as (pts_to_Some h);
      unfold (pts_to_Some h);
      assert (exists_ (fun v -> pts_to (h._1._2) #three_quart v ** pure (Some? v)));
      with v. assert (pts_to (h._1._2) #three_quart v ** pure (Some? v));
      derive_false_from_too_much_permission h._1._2 v x;
      fold (pts_to_Some h);
      rewrite (pts_to_Some h) as (task_res_own h);
      ()
    }
    else {
      ()
    }
  }
}
```

```pulse
ghost
fn fold_task_done (h:(task_elem & task_status))
  requires pts_to h._1._2 #three_quart (Some x) ** pure (h._2 = Done)
  ensures task_res_own h
{
  assert (pts_to h._1._2 #three_quart (Some x) ** pure (Some? (Some x)));
  intro_exists (fun v -> pts_to h._1._2 #three_quart v ** pure (Some? v)) (Some x);
  rewrite (exists_ (fun v -> pts_to h._1._2 #three_quart v ** pure (Some? v))) as (pts_to_Some h);
  rewrite (pts_to_Some h) as (task_res_own h);
  ()
}
```

```pulse
ghost
fn fold_tasks_res_own (h: (task_elem & task_status)) (q: mono_list_task_plus)
requires task_res_own h ** tasks_res_own q
ensures tasks_res_own (h::q)
{
  rewrite (task_res_own h ** tasks_res_own q) as (tasks_res_own (h::q));
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
(tasks_res_own l ** pts_to t._2 #three_quart (Some x))
(fun () -> tasks_res_own (close_task_bis t pos l) ** pure (
 get_actual_queue (close_task_bis t pos l) == get_actual_queue l
  /\ count_ongoing (close_task_bis t pos l) + 1 == count_ongoing l))



```pulse
ghost
fn put_back_permission
  (t: task_elem)
  (pos: nat)
  (l: (l:mono_list_task_plus{task_in_queue t pos l /\ L.length l >= 1}))
  (x: t._1)
requires tasks_res_own l ** pts_to t._2 #three_quart (Some x)
ensures tasks_res_own (close_task_bis t pos l) ** pure (
 get_actual_queue (close_task_bis t pos l) == get_actual_queue l
  /\ count_ongoing (close_task_bis t pos l) + 1 == count_ongoing l)
{
  let h = L.hd l;
  let q = L.tl l;

  unfold (tasks_res_own l);
  rewrite `@(
  match l with
    | [] -> emp
    | tl::ql -> task_res_own tl ** tasks_res_own ql)
  as (task_res_own h ** tasks_res_own q);
  assert (pts_to t._2 #three_quart (Some x));
  assert (task_res_own h ** tasks_res_own q);

  if (pos + 1 = L.length l)
  {
    assert (task_res_own h);
    rewrite (pts_to (t._2) #three_quart (Some x)) as (pts_to (h._1._2) #three_quart (Some x));
    derive_status_ongoing h (Some x);
    assert (pure (snd h = Ongoing));
    assert (pts_to (h._1._2) #three_quart (Some x));

    unfold (task_res_own h); // not needed, can be dropped
    rewrite `@(match h._2 with
      | Todo -> pts_to (h._1._2) #three_quart None
      | Ongoing -> emp
      | Done -> (exists_ (fun v -> pts_to (h._1._2) #three_quart v ** pure (Some? v))))
    as (emp);

    let h' = (h._1, Done);
    rewrite (pts_to (h._1._2) #three_quart (Some x)) as (pts_to h'._1._2 #three_quart (Some x));
    fold_task_done h';
    fold_tasks_res_own h' q;
    ()
  }
  else {
    put_back_permission_cb t pos q x;
    assert (tasks_res_own (close_task_bis t pos q));
    assert (pure (get_actual_queue (close_task_bis t pos q) == get_actual_queue q));
    assert (pure (get_actual_queue (close_task_bis t pos l) == get_actual_queue l));
    assert (pure (count_ongoing (close_task_bis t pos q) + 1 == count_ongoing q));
    assert (pure (count_ongoing (close_task_bis t pos l) + 1 == count_ongoing l));

    rewrite (task_res_own h ** tasks_res_own (close_task_bis t pos q)) as
    `@(
    match (close_task_bis t pos l) with
      | [] -> emp
      | tl::ql -> task_res_own tl ** tasks_res_own ql);
    fold (tasks_res_own (close_task_bis t pos l));
    ()
  }
}
```

// waiting to have recursion in Pulse
assume val prove_task_ongoing_aux_cb
  (t: task_elem)
  (pos: nat)
  (l: (l:mono_list_task_plus{task_in_queue t pos l /\ L.length l >= 1}))
:
stt_ghost unit emp_inames
(tasks_res_own l ** pts_to t._2 #three_quart None)
(fun () -> tasks_res_own l ** pts_to t._2 #three_quart None
  ** pure (count_ongoing l > 0))
// TODO: Implement this thing

```pulse
ghost
fn prove_task_ongoing_aux
  (t: task_elem)
  (pos: nat)
  (l: (l:mono_list_task_plus{task_in_queue t pos l /\ L.length l >= 1}))
//stt_ghost unit emp_inames
requires tasks_res_own l ** pts_to t._2 #three_quart None
ensures tasks_res_own l ** pts_to t._2 #three_quart None ** pure (count_ongoing l > 0)
{
  let h = L.hd l;
  let q = L.tl l;

  unfold (tasks_res_own l);
  rewrite `@(
  match l with
    | [] -> emp
    | tl::ql -> task_res_own tl ** tasks_res_own ql)
  as (task_res_own h ** tasks_res_own q);
  assert (pts_to t._2 #three_quart None);
  assert (task_res_own h ** tasks_res_own q);

  if (pos + 1 = L.length l)
  {
    rewrite (pts_to (t._2) #three_quart None) as (pts_to (h._1._2) #three_quart None);
    derive_status_ongoing h None;
    assert (pure (count_ongoing l > 0));
    rewrite (pts_to (h._1._2) #three_quart None) as (pts_to (t._2) #three_quart None);
    assert (pts_to t._2 #three_quart None);
    fold_tasks_res_own h q;
    ()
  }
  else {
    prove_task_ongoing_aux_cb t pos q;
    rewrite (task_res_own h ** tasks_res_own q) as
      `@(match l with
        | [] -> emp
        | tl::ql -> task_res_own tl ** tasks_res_own ql);
    fold (tasks_res_own l);
   ()
 }
}
```

```pulse
ghost
fn prove_task_ongoing'
  (#t: task_elem)
  (#pos: nat)
  (r:ghost_mono_ref task_elem)
  (q: list task_elem) (c: int)
  //(l: (l:mono_list task_elem{task_in_queue t pos l /\ L.length l >= 1})):
  (w:certificate r t pos)
//stt_ghost unit emp_inames
requires small_inv r q c ** pts_to t._2 #three_quart None
ensures small_inv r q c ** pts_to t._2 #three_quart None ** pure (c > 0)
{
  unfold small_inv r q c;
  with l. assert (pts_to_ghost_queue r l);
  let proof = recall #task_elem #t #pos r l w;
  assert (pure (task_in_queue t pos l));
  assert (pure (L.length l >= 1));
  prove_task_ongoing_aux t pos l;
  fold small_inv r q c;
  ()
}
```
let prove_task_ongoing = prove_task_ongoing'

// 3: conclude the task
```pulse
ghost
fn conclude_task_ghost'
(#t: task_elem)
(#pos: nat)
(r: ghost_mono_ref task_elem)
(q: list task_elem) (c: int)
(x: t._1)
(w: certificate r t pos)
  requires small_inv r q c ** pts_to t._2 #three_quart (Some x)
  ensures small_inv r q (c - 1) 
{
  unfold (small_inv r q c);
  with l. assert (pts_to_ghost_queue r l);
  assert (tasks_res_own l);
  assert (pure (count_ongoing l = c /\ get_actual_queue l == q));
  let proof = recall #task_elem #t #pos r l w;
  let p = close_task_bis t pos l;
  let order_is_preserved = close_task_bis_preserves_order #task_elem t pos l;
  write_ghost_queue #task_elem #l r p;
  put_back_permission t pos l x;
  assert (tasks_res_own (close_task_bis t pos l));
  fold (small_inv r q (c - 1));
  ()
}
```

let conclude_task_ghost = conclude_task_ghost'

let recall_certificate (#t: task_elem) (#pos: nat)
           (r:ghost_mono_ref task_elem)
           (v: mono_list task_elem)
           (w:certificate r t pos)
= recall r v w

// assuming recursion
assume val get_Some_finished_aux_rec
  (t: task_elem) (pos: nat)
  (l: mono_list_task_plus)
: stt_ghost t._1 emp_inames
(tasks_res_own l ** pure (task_in_queue t pos l) ** pure (count_ongoing l = 0 /\ get_actual_queue l == []))
(fun _ -> tasks_res_own l)

```pulse
ghost
fn get_Some_finished_aux
  (t: task_elem) (pos: nat)
  (l: mono_list_task_plus)
requires tasks_res_own l ** pure (task_in_queue t pos l)
  ** pure (count_ongoing l = 0 /\ get_actual_queue l == [])
returns x: t._1
ensures tasks_res_own l
{
  let h = L.hd l;
  let q = L.tl l;

  rewrite (tasks_res_own l) as (task_res_own h ** tasks_res_own q);

  if (pos + 1 = L.length l)
  {
    assert (task_res_own h);
    assert (pure (fst h == t));
    assert (pure (snd h = Done));
    rewrite (task_res_own h) as (pts_to_Some h);
    unfold (pts_to_Some h);
    with y. assert (pts_to h._1._2 #three_quart y);
    fold (pts_to_Some h);
    rewrite (pts_to_Some h) as (task_res_own h);
    rewrite (task_res_own h ** tasks_res_own q) as (tasks_res_own l);
    let x = Some?.v y;
    x
  }
  else {
    let x = get_Some_finished_aux_rec t pos q;
    rewrite (task_res_own h ** tasks_res_own q) as (tasks_res_own l);
    x
  }
}
```

let now #a (f : unit -> a) : a = f ()

```pulse
ghost
fn ghost_branch (#a:Type0) (#pre:vprop) (#post : (a -> vprop)) (b:(erased bool))
   (ft : (unit -> stt_ghost a emp_inames (pre ** pure (b == true)) post))
   (ff : (unit -> stt_ghost a emp_inames (pre ** pure (b == false)) post))
   requires pre
   returns x:a
   ensures post x
{
  let b : bool = stt_ghost_reveal _ b;
  if (b) {
    admit()
    // now ft ()
  } else {
    admit()
    // now ff ()
  }
}
```

```pulse
ghost
fn get_Some_finished'
  (#t: task_elem) (#pos: nat)
  (r:ghost_mono_ref task_elem)
  (w:certificate r t pos)
requires small_inv r [] 0
returns x: t._1
ensures small_inv r [] 0
{
  unfold small_inv r [] 0;
  with l. assert (pts_to_ghost_queue r (reveal l));
  //with c. assert (pts_to c)
  //let l : mono_list task_elem = l;
  let ll = stt_ghost_reveal _ l;
  if (L.length ll = 0) {
    admit()
  }
  else {
    admit()
  }
  (*
  recall_certificate r l w;
  assert (pure (task_in_queue t pos l));
  assert (tasks_res_own l);
  assert (pure (count_ongoing l = 0 /\ get_actual_queue l == []));
  let x = get_Some_finished_aux t pos l;
  fold small_inv r [] 0;
  x
  *)
}
```

let get_Some_finished = get_Some_finished'