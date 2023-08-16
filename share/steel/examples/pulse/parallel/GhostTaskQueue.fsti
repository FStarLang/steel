module GhostTaskQueue

module L = FStar.List.Tot.Base
module P = FStar.Preorder

// Mostly: Monotonic list of tasks with status
type task_status = | Todo | Ongoing | Done
// preorder: Todo -> Ongoing -> Done

type task_with_status (a: Type) = a & task_status
type mono_list (a: Type) = list (task_with_status a)

// the list can only evolve according to this order
// it imposes todo < ongoing < done, which we do not use
val is_mono_suffix (#a: Type): P.preorder (mono_list a)

val task_in_queue (#a: Type) (x: a) (pos:nat) (l: mono_list a): prop

val task_in_queue_preorder (#a: Type)
    (t: a) (pos: nat) (x y: mono_list a):
Lemma (requires task_in_queue t pos x /\ is_mono_suffix x y)
      (ensures task_in_queue t pos y)

let rec count_ongoing #a (l: mono_list a): nat =
match l with
| [] -> 0
| (_, s)::q -> (if s = Ongoing then 1 else 0) + count_ongoing q

let get_actual_queue #a (l: mono_list a): list a =
    L.map fst (L.filter (fun t -> Todo? (snd t)) l)

// 1. enqueue: when spawning a new task
// get a certificate for task_in_queue
val enqueue_todo (#a: Type) (l: mono_list a) (t: a):
(r:mono_list a{ get_actual_queue r == t::get_actual_queue l
                /\ count_ongoing r == count_ongoing l
                /\ r == (t, Todo)::l } &
pos:nat{task_in_queue t pos r})

val enqueue_preserves_order (#a: Type) (l: mono_list a) (t: a):
Lemma (is_mono_suffix l (enqueue_todo l t)._1)

// 2. pop: when a worker starts working on a task
// it updates the task to "ongoing"
val pop_todo_task (#a: Type) (l: mono_list a{~(get_actual_queue l == [])})
: (t:a & r:mono_list a{ get_actual_queue l == t::get_actual_queue r
                /\ count_ongoing r == count_ongoing l + 1 })

val pop_preserves_order (#a: Type) (l: mono_list a):
Lemma (requires ~(get_actual_queue l == []))
      (ensures is_mono_suffix l (pop_todo_task l)._2)

(** 3. concluding the task: when the worker is done **)
// a bit weird: Can we prove the task was not done before???
// yes, because we have the permission?
// maybe with 2/3 + 2/3 permissions
val close_task (#a: Type)
    (t: a)
    (pos: nat)
    (l: mono_list a{task_in_queue t pos l})
  : (s:task_status{L.memP (t, s) l} & r:mono_list a{
        s == Ongoing ==> (
            get_actual_queue r == get_actual_queue l /\
            count_ongoing r == count_ongoing l - 1)})

val close_task_preserves_order (#a: Type)
    (t: a) (pos: nat) (l: mono_list a{task_in_queue t pos l}):
    Lemma (is_mono_suffix l (close_task t pos l)._2 )

(** We connect the mono list with the actual queue and counter **)

let pure_inv_queue #a (q: list a) (c: int) (l: mono_list a)
= count_ongoing l = c /\ get_actual_queue l == q