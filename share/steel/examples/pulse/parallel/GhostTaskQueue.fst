module GhostTaskQueue

open FStar.List.Tot.Base
module P = FStar.Preorder

// Mostly: Monotonic list of tasks with status

type task_status = | Todo | Ongoing | Done
// preorder: Todo -> Ongoing -> Done

type task_with_status (a: Type) = a & task_status

type mono_list (a: Type) = list (task_with_status a)

(*
What we need to do:
- create empty mono_list, with counter 0, empty work_queue
- add a todo element
- change a task from 
*)

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
Lemma (is_same_mono_list x y ==> length x = length y)
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

let rec is_mono_suffix #a (x y: mono_list a): prop
= if length x < length y then is_mono_suffix x (tl y)
  else if length x = length y then is_same_mono_list x y
  else False

let is_mono_suffix_refl x:
Lemma (is_mono_suffix x x)
= is_same_refl x

let rec is_mono_suffix_trans x y z:
Lemma (requires is_mono_suffix x y /\ is_mono_suffix y z)
(ensures is_mono_suffix x z)
= if length y < length z then
    is_mono_suffix_trans x y (tl z)
  else (
    assert (length y == length z);
    if length x < length y then
        is_mono_suffix_trans x (tl y) (tl z)
    else is_same_trans x y z
  )

let rec task_in_queue #a (x: a) (l: mono_list a) =
   match l with
  | [] -> False
  | t::q -> x == fst t \/ task_in_queue x q

let rec task_in_queue_same_mono #a (t: a) (x y: mono_list a):
Lemma (requires is_same_mono_list x y)
      (ensures task_in_queue t x ==> task_in_queue t y)
= match x, y with
| tx::qx, ty::qy -> task_in_queue_same_mono t qx qy
| _ -> ()

// main reason why we want this preorder:
let rec task_in_queue_preorder #a 
    (t: a) (x y: mono_list a):
Lemma (requires task_in_queue t x /\ is_mono_suffix x y)
      (ensures task_in_queue t y)
= if length x < length y then task_in_queue_preorder t x (tl y)
  else task_in_queue_same_mono t x y

let rec count_ongoing #a (l: mono_list a): nat =
match l with
| [] -> 0
| (_, s)::q -> (if s = Ongoing then 1 else 0) + count_ongoing q

let get_actual_queue #a (l: mono_list a): list a =
    map fst (filter (fun t -> Todo? (snd t)) l)

// 1. enqueue: when spawning a new task
let enqueue_todo #a (l: mono_list a) (t: a):
(r:mono_list a{ get_actual_queue r == t::get_actual_queue l
                /\ count_ongoing r == count_ongoing l })
= (t, Todo)::l

let enqueue_preserves_order l t:
Lemma (is_mono_suffix l (enqueue_todo l t))
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
    (eq: (x:a -> y:a -> b:bool{b <==> x == y }))
    (t: a)
    (l: mono_list a{task_in_queue t l}):
    (s:task_status{memP (t, s) l} & r:mono_list a{
        s == Ongoing ==> (
            get_actual_queue r == get_actual_queue l /\
            count_ongoing r == count_ongoing l - 1)})
= match l with
| (t', s)::q -> if eq t t' then (| s, (t', Done)::q |)
else let (| s', q' |) = close_task eq t q in (| s', (t', s)::q' |)

let rec close_task_preserves_order_aux #a
    (eq: (x:a -> y:a -> b:bool{b <==> x == y }))
    (t: a)
    (l: mono_list a{task_in_queue t l}):
    Lemma (is_same_mono_list l (close_task eq t l)._2 )
= match l with
| (t', s)::q -> if eq t t' then is_mono_suffix_refl q
else let (| s', q' |) = close_task eq t q in close_task_preserves_order_aux eq t q

let close_task_preserves_order #a
    (eq: (x:a -> y:a -> b:bool{b <==> x == y }))
    (t: a)
    (l: mono_list a{task_in_queue t l}):
    Lemma (is_mono_suffix l (close_task eq t l)._2 )
= close_task_preserves_order_aux eq t l; from_same_to_suffix l (close_task eq t l)._2


(** We connect the mono list with the actual queue and counter **)



let pure_inv_queue #a (q: list a) (c: int) (l: mono_list a)
= count_ongoing l = c /\ get_actual_queue l == q


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