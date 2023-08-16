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
let rec close_task #a
    //(eq: (x:a -> y:a -> b:bool{b <==> x == y }))
    (t: a)
    (pos: nat)
    (l: mono_list a{task_in_queue t pos l}):
    (s:task_status{L.memP (t, s) l} & r:mono_list a{
        s == Ongoing ==> (
            get_actual_queue r == get_actual_queue l /\
            count_ongoing r == count_ongoing l - 1)})
= match l with
| (t', s)::q -> 
//if eq t t'
if pos + 1 = L.length l
  then (| s, (t', Done)::q |)
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

// in NewDomains, g is ._3 and f is ._1
let task_res_own (t: task_plus): vprop
= match t._2 with
| Todo -> pts_to (t._1._2) #three_quart None
| Ongoing -> emp // in this case, the worker has the half permission
| Done -> (exists_ (fun v -> pts_to (t._1._2) #three_quart v ** pure (Some? v)))

let mono_list_task_plus: Type u#1 = mono_list task_elem
  
let rec tasks_res_own (l: mono_list_task_plus): vprop
=  match l with
  | [] -> emp
  | tl::ql -> task_res_own tl ** tasks_res_own ql

```pulse
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