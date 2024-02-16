module GhostTaskQueue

module L = FStar.List.Tot.Base
module P = FStar.Preorder
module GR = Pulse.Lib.GhostReference

open SingleGhostTask


let rec is_same_mono_list (x y: mono_list) =
match x, y with
| [], [] -> True
| tx::qx, ty::qy ->
(*  tx._1 == ty._1 /\ tx._3 = ty._3 /\ tx._4 == ty._4 /\ tx._5 == ty._5 /\ is_same_mono_list qx qy *)
same_extended_tasks tx ty /\ is_same_mono_list qx qy
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

let rec is_mono_suffix' (x y: mono_list): prop
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

//val is_mono_suffix (#a: Type): P.preorder (mono_list)

let is_mono_suffix: P.preorder mono_list =
  introduce forall x. (is_mono_suffix' x x) with (is_mono_suffix_refl x);
  introduce forall x y z. (is_mono_suffix' x y /\ is_mono_suffix' y z
    ==> is_mono_suffix' x z) with (
  introduce (is_mono_suffix' x y /\ is_mono_suffix' y z)
    ==> is_mono_suffix' x z
    with _. (is_mono_suffix_trans x y z)
  );
  is_mono_suffix'

//val task_in_queue (#a: Type) (x: a) (pos:nat) (l: mono_list): prop

let task_plus a = a & GR.ref bool & GR.ref bool & GR.ref bool

let rec task_in_queue (x: task) (pos:nat) (l: mono_list): prop =
  if pos + 1 = L.length l then
    (L.hd l)._1 == x
  else if pos + 1 < L.length l then
    task_in_queue x pos (L.tl l)
  else False

let rec task_in_queue_same_mono (t: task) (pos:nat) (x y: mono_list):
Lemma (requires is_same_mono_list x y)
      (ensures task_in_queue t pos x ==> task_in_queue t pos y)
= is_same_mono_same_length x y;
  if pos + 1 < L.length x then
    task_in_queue_same_mono t pos (L.tl x) (L.tl y)
  else ()

// main reason why we want this preorder:
let rec task_in_queue_preorder
    (t: task) (pos: nat) (x y: mono_list):
Lemma (requires task_in_queue t pos x /\ is_mono_suffix x y)
      (ensures task_in_queue t pos y)
= if L.length x < L.length y then task_in_queue_preorder t pos x (L.tl y)
  else task_in_queue_same_mono t pos x y

// 1. enqueue: when spawning a new task
// get a certificate for task_in_queue
let enqueue_todo (l: mono_list) (t: task)
(*
(r:mono_list{ get_actual_queue r == t::get_actual_queue l
                /\ count_ongoing r == count_ongoing l } &
pos:nat{task_in_queue t pos r})
*)
= (| (t, Todo)::l, L.length l |)

let enqueue_preserves_order l (t: task):
Lemma (is_mono_suffix l (enqueue_todo l t)._1)
= is_same_refl l

let rec count_ongoing (l: mono_list): nat =
match l with
| [] -> 0
| t::q -> (if t._2 = Ongoing then 1 else 0) + count_ongoing q

let get_actual_queue (l: mono_list): list task =
    L.map (fun (t: extended_task) -> t._1) (L.filter is_Todo l)

// 2. pop: when a worker starts working on a task
// it updates the task to "ongoing"
let rec pop_todo_task (l: mono_list{~(get_actual_queue l == [])})
: (t:task & r:mono_list{ get_actual_queue l == t::get_actual_queue r
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

let rec close_task
    (t: task)
    (pos: nat)
    (l: mono_list{task_in_queue t pos l /\ L.length l >= 1}):
    (s:task_status{L.memP (t, s) l} & r:mono_list{
        s == Ongoing ==> (
            get_actual_queue r == get_actual_queue l /\
            count_ongoing r == count_ongoing l - 1)})
= let (t', s)::q = l in
if pos + 1 = L.length l
  then (| s, (t', Done)::q |) // if s is not Ongoing, then we have too much permission
  else let (| s', q' |) = close_task t pos q in (| s', (t', s)::q' |)

let rec close_task_preserves_order_aux
    (t: task)
    (pos: nat)
    (l: mono_list{task_in_queue t pos l}):
    Lemma (is_same_mono_list l (close_task t pos l)._2 )
= match l with
| (t', s)::q -> if pos + 1 = L.length l then is_mono_suffix_refl q
else let (| s', q' |) = close_task t pos q in close_task_preserves_order_aux t pos q

let close_task_preserves_order
    (t: task)
    (pos: nat)
    (l: mono_list{task_in_queue t pos l}):
    Lemma (is_mono_suffix l (close_task t pos l)._2 )
= close_task_preserves_order_aux t pos l; from_same_to_suffix l (close_task t pos l)._2




(** ------------------------------------------------------
Part 2: Instantiation as a ghost monotonic reference
------------------------------------------------------ **)

module M = Pulse.Lib.GhostMonotonicHigherReference
open Pulse.Lib.Pervasives

#push-options "--print_universes"

//unfold
let ghost_mono_ref = M.ref mono_list is_mono_suffix

(*
let pts_to_ghost_queue #a (r: ghost_mono_ref) (l: mono_list): vprop
= M.pts_to r full_perm l

//open Pulse.Lib.Pervasives

let pts_to_ghost_queue_half #a (r: ghost_mono_ref) (l: mono_list): vprop
= M.pts_to r one_half l
*)

(* Share/gather specialized to half permission *)
val mono_share2 (#a:Type) (r:ghost_mono_ref) (#v:erased (mono_list))
  : stt_ghost unit
      (M.pts_to r full_perm v)
      (fun _ -> M.pts_to r one_half v ** M.pts_to r one_half v)

val mono_gather2 (#a:Type) (r:ghost_mono_ref) (#x0 #x1: erased (mono_list))
  : stt_ghost unit
      (M.pts_to r one_half x0 ** M.pts_to r one_half x1)
      (fun _ -> M.pts_to r full_perm x0 ** pure (x0 == x1))

let task_in_queue_stable t pos:
Lemma (P.stable (task_in_queue t pos) is_mono_suffix)
= introduce forall x y. (task_in_queue t pos x /\ is_mono_suffix x y
==> task_in_queue t pos y) with
  (introduce (task_in_queue t pos x /\ is_mono_suffix x y)
  ==> task_in_queue t pos y with _. task_in_queue_preorder t pos x y)

// can witness that task is in queue
let witness #t #pos
            (r:ghost_mono_ref)
            (v:erased (mono_list))
            (_:squash (task_in_queue t pos v))
  : //TODO: SteelAtomicUT
  stt_ghost (M.witnessed r (task_in_queue t pos)) 
                  (M.pts_to r full_perm v)
                  (fun _ -> M.pts_to r full_perm v)
= task_in_queue_stable t pos ; M.witness r (task_in_queue t pos) v _

let recall #t #pos
           (r:ghost_mono_ref)
           (v:erased (mono_list))
           (w:M.witnessed r (task_in_queue t pos))
  : //TODO: SteelAtomicU
 stt_ghost unit 
                 (M.pts_to r one_half v)
                 (fun _ -> M.pts_to r one_half v ** pure (task_in_queue t pos v))
  = M.recall (task_in_queue t pos) r v w

let recall_full #t #pos
           (r:ghost_mono_ref)
           (v:erased (mono_list))
           (w:M.witnessed r (task_in_queue t pos))
  : //TODO: SteelAtomicU
 stt_ghost unit 
                 (M.pts_to r full_perm v)
                 (fun _ -> M.pts_to r full_perm v ** pure (task_in_queue t pos v))
  = M.recall (task_in_queue t pos) r v w




(** Part 3: Associated permissions: Reasoning done here **)

module Lock = Pulse.Lib.SpinLock

(*
let task: Type u#1 = (
  a: Type0 // return type of the computation
  & r: ref (option a) // the reference where we put the result of the computation
  & Lock.lock (own_res r)//(exists_ (fun v -> pts_to r half v ** (if None? v then pts_to r half v else emp)))
  //& (unit_emp_stt_pure_pure a)
  // to create this thing
)

let task_plus: Type u#1 = task_with_status task

let mono_list_task_plus: Type u#1 = mono_list task
*)

let certificate (r:ghost_mono_ref) (t: task) (pos: nat)
= M.witnessed r (task_in_queue t pos)

// can witness that task is in queue
let get_certificate (t: task) (pos: nat)
            (r:ghost_mono_ref)
            (l:mono_list)
            (_:squash (task_in_queue t pos l))
  : //TODO: SteelAtomicUT
  stt_ghost (certificate r t pos)
                  (M.pts_to r full_perm l)
                  (fun _ -> M.pts_to r full_perm l)
= witness r l _









#pop-options

let inv_ghost_queue (r: ghost_mono_ref): vprop =
  exists* l. M.pts_to r one_half l ** tasks_res l

```pulse
ghost
fn add_todo_task (t: task) (l:mono_list)
  requires GR.pts_to t._1 #one_half true ** GR.pts_to t._2 #one_half false ** pts_to t._4 #one_half false ** GR.pts_to t._5 #one_half false
   ** tasks_res l
  ensures tasks_res (enqueue_todo l t)._1
{
  get_task_res_todo t;
  assert (task_res (t, Todo) ** tasks_res l);
  rewrite (task_res (t, Todo) ** tasks_res l) as tasks_res (enqueue_todo l t)._1;
  ()
}
```

(*
Needed:
0. Create ghost queue empty, invariant (with half permission)
We give back the other half

1. We add a task, get a certificate

2. We get a task, and switch it from todo to ongoing

3. We turn an ongoing task to todo

4. We claim? We create the pledges?
*)

(* TD: Current progress here... *)

(*
// 1. create queue, alloc inv
```pulse
unobservable fn init_ghost_queue' (_: unit)
requires emp
returns res: (r:ghost_mono_ref & inv (inv_ghost_queue r))
ensures M.pts_to res._1 one_half []
{
  let r = M.alloc #_ #is_mono_suffix [];

  admit()
  (*
  let l: mono_list task = [(t, Todo)];
  let r': M.ref (mono_list task) is_mono_suffix = M.alloc #emp_inames #_ (is_mono_suffix) l;
  assert (M.pts_to r' full_perm l);
  let r: gmref = convert_to_ghost_mono_ref r';

  rewrite (M.pts_to r' full_perm l) as (M.pts_to r full_perm l);
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
  rewrite (M.pts_to r one_half l ** tasks_res_own l one_quart)
    as `@(if 1 = 0 && L.length [t] = 0 then deadline r
  else M.pts_to r one_half l ** tasks_res_own l one_quart);
  fold small_inv r [t] 0;
  rewrite (small_inv r [t] 0) as (small_inv (reveal pair)._1 [t] 0);
  pair
  *)
}
```

let init_ghost_queue = init_ghost_queue'























(*

// assuming because of universe polymorphism
assume val
stt_return #a (x:a): stt a emp (fun y -> pure (x == y))

// assuming because of universe polymorphism
assume val
stt_return_ghost #a (x:a): stt_ghost a emp_inames emp (fun y -> pure (x == y))
*)



#push-options "--print_universes --print_implicits"

    



(*
```pulse
ghost
fn prove_task_ongoing_aux
  (t: task)
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
  (#t: task)
  (#pos: nat)
  (#v: option t._1)
  (r: gmref)
  (q: list task) (c: int)
  //(l: (l:mono_list task{task_in_queue t pos l /\ L.length l >= 1})):
  (w:certificate r t pos)
//stt_ghost unit emp_inames
requires small_inv r q c ** pts_to t._2 #three_quart v
ensures small_inv r q c ** pts_to t._2 #three_quart v ** pure (c > 0)
{
  unfold small_inv r q c;
  with l. assert (M.pts_to r one_half l);
  let proof = recall #task #t #pos r l w;
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

let convert_to_ghost_mono_ref (r: M.ref (mono_list task) is_mono_suffix):
  gmref
  //ghost_mono_ref
  = r

  *)




// 1: Enqueue
```pulse
ghost
fn spawn_task_ghost'
(r: gmref)
(q: list task) (c: int) (t: task)
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

  with vl. assert (M.pts_to r full_perm vl);
  assert (tasks_res_own vl three_quart);
  assert (pure (count_ongoing vl = c /\ get_actual_queue vl == q));
  let p = enqueue_todo #task vl t;
  let pos = p._2;
  assert (pure (task_in_queue t pos p._1));
  write_ghost_queue #task #vl r p._1;
  assert (M.pts_to r full_perm p._1);
  let w: certificate r t pos = get_certificate t pos r p._1 _;
  assert (tasks_res_own vl three_quart);
  fold_done_task t vl three_quart;
  assert (tasks_res_own (enqueue_todo vl t)._1 three_quart);
  assert (M.pts_to r full_perm p._1);
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
(t: task)
(q: list task) (c: int)
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
  with l. assert (M.pts_to r full_perm l);
  assert (tasks_res_own l three_quart);
  assert (pure (count_ongoing l = c /\ get_actual_queue l == t::q));
  let p = pop_todo_task #task l;
  let order_is_preserved = pop_preserves_order #task l;
  write_ghost_queue #task #l r p._2;
  assert (M.pts_to r full_perm p._2);
  let certif: certificate r t p._3 = get_certificate t p._3 r p._2 ();
  assert (M.pts_to r full_perm p._2);
  assert (pure (p._1 == t));
  get_permission_from_todo l three_quart;
  (*
requires exists l. (M.pts_to r full_perm l
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
    (l: mono_list{task_in_queue t pos l /\ L.length l >= 1}):
  mono_list
= let (t', s)::q = l in
if pos + 1 = L.length l
  then (t', Done)::q // if s is not Ongoing, then we have too much permission
  else (t', s)::(close_task_bis t pos q)

let rec close_task_bis_preserves_order_aux #a
    (t: a)
    (pos: nat)
    (l: mono_list{task_in_queue t pos l}):
    Lemma (is_same_mono_list l (close_task_bis t pos l) )
= match l with
| (t', s)::q -> if pos + 1 = L.length l then is_mono_suffix_refl q
else let q' = close_task_bis t pos q in close_task_bis_preserves_order_aux t pos q



let close_task_bis_preserves_order #a
    (t: a)
    (pos: nat)
    (l: mono_list{task_in_queue t pos l}):
    Lemma (is_mono_suffix l (close_task_bis t pos l) )
= close_task_bis_preserves_order_aux t pos l; from_same_to_suffix l (close_task_bis t pos l)


```pulse
ghost
fn fold_task_done (h:(task & task_status)) (f: perm)
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
  (t: task)
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
  (h: (task & task_status)) 
  (h': (task & task_status))
  (q: mono_list_task_plus)
 (pos: nat) (t: task)
(l: (l:mono_list_task_plus{task_in_queue t pos l /\ b2t (L.length l >= 1)}))
requires task_res_own h' three_quart ** tasks_res_own q three_quart
  ** pure (t == h._1 /\ h == L.hd l /\ q == L.tl l /\ h' == (h._1, Done)
  /\ pos + 1 = L.length l
  )
  //** pure (t == h._1 /\ h == L.hd l /\ q == L.tl l)
//ensures tasks_res_own (h::q) f
ensures tasks_res_own (close_task_bis u#1 #task t pos l) three_quart
{
  rewrite (task_res_own h' three_quart ** tasks_res_own q three_quart) as (tasks_res_own (h'::q) three_quart);
  rewrite (tasks_res_own (h'::q) three_quart)
    as (tasks_res_own (close_task_bis u#1 #task t pos l) three_quart);
  ()
}
```




```pulse
ghost
fn put_back_permission
  (t: task)
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
    assert (tasks_res_own (close_task_bis u#1 #task t pos l) three_quart);
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
  (q: list task) (c: int)
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
(#t: task)
(#pos: nat)
(r: gmref)
(q: list task) (c: int)
(x: t._1)
(w: certificate r t pos)
  requires small_inv r q c ** pts_to t._2 #three_quart (Some x)
  ensures small_inv r q (c - 1) //** imp_vprop (c = 1 && L.length q = 0) (deadline r)
{
  prove_task_ongoing' #t #pos #(Some x) r q c w;
  assert (pure (c > 0));
  unfold_small_inv r q c;
  //unfold (small_inv r q c);
  with l. assert (M.pts_to r full_perm l);
  assert (tasks_res_own l three_quart);
  assert (pure (count_ongoing l = c /\ get_actual_queue l == q));
  let proof = recall_full #task #t #pos r l w;
  let p = close_task_bis t pos l;
  let order_is_preserved = close_task_bis_preserves_order #task t pos l;
  write_ghost_queue #task #l r p;
  assert (M.pts_to r full_perm p);

  put_back_permission t pos l x;
  assert (tasks_res_own (close_task_bis t pos l) three_quart);

  rewrite (tasks_res_own (close_task_bis u#1 #task t pos (reveal u#1 #(mono_list u#1 task) l)) three_quart)
    as (tasks_res_own p three_quart);

  assert (M.pts_to r full_perm p);
  assert (pure (c - 1 = count_ongoing p /\ q == get_actual_queue p));

  let b: bool = stt_ghost_reveal _ (c - 1 = 0 && L.length q = 0);
  if (b)
  {
    share_queue r p;
    share_tasks_res_own p;
    obtain_deadline r one_quart;
    duplicate_deadline r;

    assert (M.pts_to r one_half p);
    //assert (tasks_res_own p one_half ** tasks_res_own p one_quart);
    rewrite (deadline r)
      as `@(if c - 1 = 0 && L.length q = 0 then deadline r
      else M.pts_to r one_half l ** tasks_res_own l one_quart);

    assert (M.pts_to r one_half p **
      tasks_res_own p one_half **
      pure (count_ongoing p = c - 1 /\ get_actual_queue p == q)
      ** `@(if c - 1 = 0 && L.length q = 0 then deadline r
      else M.pts_to r one_half p ** tasks_res_own p one_quart));
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

let recall_certificate (#t: task) (#pos: nat)
           (r:ghost_mono_ref)
           (v: mono_list task)
           (w:certificate r t pos)
= recall_full r v w


let pts_to_Some_fract (t:task) (f: perm): vprop
= (exists_ (fun v -> pts_to t._2 #f v ** pure (Some? v)))

// assuming recursion
assume val get_Some_finished_aux_rec
  (t: task) (pos: nat)
  (l: mono_list_task_plus)
  (f: perm)
: stt_ghost unit emp_inames
(tasks_res_own l f ** pure (task_in_queue t pos l) ** pure (count_ongoing l = 0 /\ get_actual_queue l == []))
(fun _ -> tasks_res_own l (half_perm f) ** pts_to_Some_fract t (half_perm f))

```pulse
ghost
fn get_Some_finished_aux
  (t: task) (pos: nat)
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
fn fold_task_done (h:(task & task_status)) (f: perm)
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

let recall_certificate_fract (#t: task) (#pos: nat)
           (r:ghost_mono_ref)
           (v: mono_list task)
           (w:certificate r t pos)
           (f: perm):
 stt_ghost unit emp_inames
                 (M.pts_to r f v)
                 (fun _ -> M.pts_to r f v ** pure (task_in_queue t pos v))
  = M.recall (task_in_queue t pos) r v w



```pulse
ghost fn
proof_promise' (#t: task) (#pos: nat)
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

*)