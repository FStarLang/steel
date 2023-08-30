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
                /\ count_ongoing r == count_ongoing l + 1 }
  & pos:nat{task_in_queue t pos r})

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

open Pulse.Lib.Pervasives

module Lock = Pulse.Lib.SpinLock

let one_quart = half_perm (half_perm full_perm)

let own_res (#a: Type0) (r: ref (option a)) = (exists_ (fun v -> pts_to r #one_quart v))

let three_quart = sum_perm (half_perm full_perm) (half_perm (half_perm full_perm))

let own_None r = pts_to r #three_quart None
//let is_active (p: par_env): vprop = pts_to p._5._1._2 #three_quart None

//let current_task r = (t:task_elem & pos:nat & certificate r t pos)

let task_elem: Type u#1 = (
  a: Type0 // return type of the computation
  & r: ref (option a) // the reference where we put the result of the computation
  & Lock.lock (own_res r)//(exists_ (fun v -> pts_to r half v ** (if None? v then pts_to r half v else emp)))
  //& (unit_emp_stt_pure_pure a)
  // to create this thing
)

val ghost_mono_ref (a: Type u#1): Type0

val pts_to_ghost_queue (#a: Type) (r: ghost_mono_ref a) (l: mono_list a): vprop

val certificate (r:ghost_mono_ref task_elem) (t: task_elem) (pos: nat): Type0

val small_inv (r: ghost_mono_ref task_elem) (q: list task_elem) (c: int): vprop 

// 1. enqueue task
val spawn_task_ghost
(r: ghost_mono_ref task_elem)
(q: list task_elem) (c: int) (t: task_elem):
stt_ghost (erased (pos:nat & certificate r t pos)) emp_inames
(small_inv r q c ** pts_to t._2 #three_quart None)
(fun _ -> small_inv r (t::q) c)

// 2. pop task todo
// return certificate?
val pop_task_ghost
(r: ghost_mono_ref task_elem)
(t: task_elem)
(q: list task_elem) (c: int):
stt_ghost (erased (pos:nat & certificate r t pos)) emp_inames
(small_inv r (t::q) c)
(fun _ -> small_inv r q (c + 1) ** pts_to t._2 #three_quart None)

val prove_task_ongoing
  (#t: task_elem)
  (#pos: nat)
  (#v: option t._1)
  (r:ghost_mono_ref task_elem)
  (q: list task_elem) (c: int)
  //(l: (l:mono_list task_elem{task_in_queue t pos l /\ L.length l >= 1})):
  (w:certificate r t pos):
stt_ghost unit emp_inames
(small_inv r q c ** pts_to t._2 #three_quart v)
(fun () -> small_inv r q c ** pts_to t._2 #three_quart v ** pure (c > 0))

val prove_ongoing_non_neg
  (r:ghost_mono_ref task_elem)
  (q: list task_elem) (c: int)
: stt_ghost unit emp_inames
(small_inv r q c)
(fun () -> small_inv r q c ** pure (c >= 0))

// 3. conclude a task
val conclude_task_ghost
(#t: task_elem)
(#pos: nat)
(r: ghost_mono_ref task_elem)
(q: list task_elem) (c: int)
(x: t._1)
(w: certificate r t pos):
stt_ghost unit emp_inames
(small_inv r q c ** pts_to t._2 #three_quart (Some x))
(fun () -> small_inv r q (c - 1))


val recall_certificate (#t: task_elem) (#pos: nat)
           (r:ghost_mono_ref task_elem)
           (v: mono_list task_elem)
           (w:certificate r t pos)
  : //TODO: SteelAtomicU
 stt_ghost unit emp_inames
                 (pts_to_ghost_queue r v)
                 (fun _ -> pts_to_ghost_queue r v ** pure (task_in_queue t pos v))

val get_Some_finished (#t: task_elem) (#pos: nat)
  (r:ghost_mono_ref task_elem)
  (w:certificate r t pos)
: stt_ghost t._1 emp_inames
(small_inv r [] 0)
// that's the proof that it's finished
(fun _ -> small_inv r [] 0)