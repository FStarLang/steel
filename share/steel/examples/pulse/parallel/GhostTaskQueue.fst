module GhostTaskQueue

module L = FStar.List.Tot.Base
module P = FStar.Preorder

//#push-options "--fuel 10 --ifuel 10 --z3rlimit 10"
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

// [..., ..., task] -> pos 0
// [task, ...] -> pos 1
// l[length l - (pos_task + 1)] = task
// length l - pos_task - 1 >= 0
// pos_task < length l
// if pos_task + 1 == length l --> we're there!

let rec task_in_queue #a (x: a) (pos:nat) (l: mono_list a) =
  if pos + 1 = L.length l then
    fst (L.hd l) == x
  else if pos + 1 < L.length l then
    task_in_queue x pos (L.tl l)
  else False


  //x == fst (L.index l (L.length l - pos - 1))
  (*
  if pos + 1 = length l then // we're there
   match l with
  | [] -> False
  | t::q -> x == fst t \/ task_in_queue x q
  *)

let rec task_in_queue_same_mono #a (t: a) (pos:nat) (x y: mono_list a):
Lemma (requires is_same_mono_list x y)
      (ensures task_in_queue t pos x ==> task_in_queue t pos y)
= is_same_mono_same_length x y;
  if pos + 1 < L.length x then
    task_in_queue_same_mono t pos (L.tl x) (L.tl y)
  else ()
(*
match x, y with
| tx::qx, ty::qy -> task_in_queue_same_mono t pos qx qy
| _ -> ()
*)

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
// a bit weird: Can we prove the task was not done before???
// yes, because we have the permission?
// maybe with 2/3 + 2/3 permissions
// do I need an id (with distinctness) to compare two tasks?
// If equality does not work, can add indices, with a uniqueness invariant...
let task_in_queue_not_empty t pos l:
  Lemma (requires task_in_queue t pos l)
        (ensures L.length l >= 1)
= ()

let rec close_task #a
    //(eq: (x:a -> y:a -> b:bool{b <==> x == y }))
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
            //(fact:stable_property p)
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

unfold
let one_quart = half_perm (half_perm full_perm)

unfold
let three_quart = sum_perm (half_perm full_perm) (half_perm (half_perm full_perm))

let own_res (#a: Type0) (r: ref (option a)) = (exists_ (fun v -> pts_to r #one_quart v))

let unit_emp_stt_pure_pure a
  = unit -> stt a emp (fun _ -> emp)

let task_elem: Type u#1 = (
  a: Type0 // return type of the computation
  & r: ref (option a) // the reference where we put the result of the computation
  & Lock.lock (own_res r)//(exists_ (fun v -> pts_to r half v ** (if None? v then pts_to r half v else emp)))
  & (unit_emp_stt_pure_pure a)
)

let task_plus: Type u#1 = task_with_status task_elem

let mono_list_task_plus: Type u#1 = mono_list task_elem

let certificate (r:ghost_mono_ref task_elem) (t: task_elem) (pos: nat)
= M.witnessed r (task_in_queue t pos)

// can witness that task is in queue
let get_certificate (t: task_elem) (pos: nat)
            (r:ghost_mono_ref task_elem)
            //(fact:stable_property p)
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


// in NewDomains, g is ._3 and f is ._1
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
fn spawn_task_ghost
(r: ghost_mono_ref task_elem)
(q: list task_elem) (c: int) (t: task_elem)
  requires small_inv r q c ** pts_to t._2 #three_quart None 
  returns w: (pos:nat & certificate r t pos)
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
  let res = (| pos, w |);
  res
}
```

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
fn pop_task_ghost
(r: ghost_mono_ref task_elem)
(t: task_elem)
(q: list task_elem) (c: int) (t: task_elem)
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

// To prove
assume val equiv_not_aliases (#a: Type) (r1 r2: ref a) (v1 v2: a):
vprop_equiv
  (pts_to r1 #three_quart v1 ** pts_to r2 #three_quart v2)
  (pts_to r1 #three_quart v1 ** pts_to r2 #three_quart v2 ** pure (~(r1 == r2)))

let derive_false_from_too_much_permission (#a: Type) (r: ref a) (v1 v2: a):
stt_ghost unit emp_inames (pts_to r #three_quart v1 ** pts_to r #three_quart v2)
(fun () ->
pts_to r #three_quart v1 ** pts_to r #three_quart v2 **
pure (~(r == r)))
= rewrite _ _ (equiv_not_aliases r r v1 v2)


// TODO: Do this vprop_equiv

(*
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
*)

(*
let rec put_back_permission_equiv
  (t: task_elem)
  (pos: nat)
  (l: mono_list_task_plus{task_in_queue t pos l})
  (x: t._1)
: vprop_equiv 
  (tasks_res_own l ** pts_to t._2 #three_quart (Some x))
  (tasks_res_own (close_task t pos l)._2 **
  pure (Ongoing? (close_task t pos l)._1))
= match l with
| (t', s)::q -> 
if pos + 1 = L.length l
  then admit() //(| s, (t', Done)::q |)
  else let (| s', q' |) = close_task t pos q in
  assert (close_task t pos l == (| s', (t', s)::q' |));
  admit() // (| s', (t', s)::q' |)
  *)

  (*
   match l with
| (t', s)::q -> 
//if eq t t'
if pos + 1 = L.length l
  then (| s, (t', Done)::q |) // if s is not Ongoing, then we have too much permission
  else let (| s', q' |) = close_task t pos q in (| s', (t', s)::q' |)
  *)

(*
= match l with
| (t', s)::q -> 
//if eq t t'
if pos + 1 = L.length l
  then (| s, (t', Done)::q |)
  else let (| s', q' |) = close_task t pos q in (| s', (t', s)::q' |)
*)
//let decompose_list (l: mono_list_task_plus{L.length l > 0}):
//  Lemma (L.hd l == ((L.hd l)._1, (L.hd l)._2))
//  = ()
let rec close_task_bis #a
    //(eq: (x:a -> y:a -> b:bool{b <==> x == y }))
    (t: a)
    (pos: nat)
    (l: mono_list a{task_in_queue t pos l /\ L.length l >= 1}):
  mono_list a
  (*
    (s:task_status{L.memP (t, s) l} & r:
    mono_list a{
        s == Ongoing ==> (
            get_actual_queue r == get_actual_queue l /\
            count_ongoing r == count_ongoing l - 1)})
*)
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
fn derive_status_ongoing (h: (task_elem & task_status)) (x: h._1._1)
  requires task_res_own h ** (pts_to (h._1._2) #three_quart (Some x))
  ensures task_res_own h ** (pts_to (h._1._2) #three_quart (Some x)) ** pure (h._2 = Ongoing)
{
  if (snd h = Todo) {
    rewrite (task_res_own h) as (pts_to (h._1._2) #three_quart None);
    derive_false_from_too_much_permission h._1._2 None (Some x);
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
      ////with v. assert (pts_to h._1._2 v);
      derive_false_from_too_much_permission h._1._2 v (Some x);
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
(*
    let h' = (h._1, Done);
    rewrite (pts_to (h._1._2) #three_quart (Some x)) as (pts_to h'._1._2 #three_quart (Some x));
    //rewrite (pts_to h'._1._2 #three_quart (Some x)) as
     // (exists v. pts_to (h'._1._2) #three_quart v ** pure (Some? v));

    rewrite (pts_to (h._1._2) #three_quart (Some x))
    as `@(match h'._2 with
      | Todo -> pts_to (h'._1._2) #three_quart None
      | Ongoing -> emp
      | Done -> (exists_ (fun v -> pts_to (h'._1._2) #three_quart v ** pure (Some? v))));
    *)

```pulse
ghost
fn fold_tasks_res_own (h: (task_elem & task_status)) (q: mono_list_task_plus)
//: stt_ghost unit emp_inames
requires task_res_own h ** tasks_res_own q
ensures tasks_res_own (h::q)
{
  rewrite (task_res_own h ** tasks_res_own q) as (tasks_res_own (h::q));
  ()
}
```
//= rewrite ()

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
    derive_status_ongoing h x;
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

(*
  //Ongoing? (close_task t pos l)._1)
{
  assert (pure (L.length l > 0));
  (*
= let (t', s)::q = l in
if pos + 1 = L.length l
  then (| s, (t', Done)::q |) // if s is not Ongoing, then we have too much permission
  else let (| s', q' |) = close_task t pos q in (| s', (t', s)::q' |)
  *)
  //let h: ((task_elem u#1) & task_status) = L.hd l;
  let h: (task_with_status u#1 task_elem) = L.hd l;
// type task_with_status (a: Type) = a & task_status
  let t': task_elem = fst h;
  let s: task_status = snd h;
  //assert (pure (h == (t', s)));
  assert (pure (fst h == t'));
  assert (pure (snd h == s));
  assert (pure (eq2 h (Mktuple2 #task_elem #task_status t' s)));

  let q = L.tl l;
  //assert (pure (l == (t', s)::q));
  //assert (pure (h == (t', s)));
  //let proof = decompose_list l;
  //rewrite emp as (pure (L.hd l == (t', s)));
  //assert (pure (L.hd l == (t', s))); // why needed?
  assert (pure (l == (L.hd l)::q));
  //assert (pure (l == (t', s)::q));
  //inhale (pure (L.hd l == (t', s))); // why needed?
  //rewrite emp as (pure (l == ((t', s)::q))); // unclear...
  //assert (pure (l == ((t', s)::q))); // unclear...
  //inhale (pure ( l == (t', s)::q ));
  //inhale (pure ( l == (t', s)::q ));
  if (pos + 1 = L.length l)
  {
    let pair: (tuple2 u#1 u#0 task_elem task_status) = Mktuple2 #task_elem #task_status t' Done;
    let pairq = Cons #(tuple2 u#1 u#0 task_elem task_status) pair q;
    let dtup = Mkdtuple2 #task_status #_ s pairq;
    assert (pure (close_task t pos l == dtup));
    // task must be t
    // status can be only Ongoing, otherwise we derive a contradiction
    admit()
  }
  else
  {
    // recursive call
    admit()
  }
  (*
= match l with
| (t', s)::q -> 
if pos + 1 = L.length l
  then admit() //(| s, (t', Done)::q |)
  else let (| s', q' |) = close_task t pos q in admit() // (| s', (t', s)::q' |)
  *)
}
```
*)




// 3: conclude the task
```pulse
ghost
fn conclude_task_ghost
(t: task_elem)
(pos: nat)
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


(*
Need:
1. Being able to enqueue, and return witnessed
2. Being able to pop
3. Being able to set task to done
*)

(** We connect the mono list with the actual queue and counter **)


(*
let rec pure_inv_mono t q c l
  : Lemma
  (requires pure_inv_queue q c l)
  (ensures pure_inv_queue (t::q) c l)
  (decreases l)
= match l with
  | [] -> ()
  | tl::ql -> pure_inv_mono t q (decrement_if_ongoing tl c) ql






let decrement_if_ongoing #a (t: task_with_status a) (c: int)
= if Ongoing? t._2 then c - 1 else c

// if we filter only the TODOs, we have the queue?

// Checks two things:
// 1. every "Todo" task must be in the work queue
// 2. the counter should equal the number of "Ongoing" tasks
let rec pure_inv_queue #a (q: list a) (c: int) (l: mono_list a):
  Tot prop (decreases l)
= match l with
  | [] -> c = 0
  | tl::ql -> ((Todo? tl._2 ==> memP tl._1 q) /\ pure_inv_queue q (decrement_if_ongoing tl c) ql)

(** Lemmas **)
let rec pure_inv_mono t q c l
  : Lemma
  (requires pure_inv_queue q c l)
  (ensures pure_inv_queue (t::q) c l)
  (decreases l)
= match l with
  | [] -> ()
  | tl::ql -> pure_inv_mono t q (decrement_if_ongoing tl c) ql

*)