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

let x = ()

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

let enqueue_preserves_order l (t: task):
Lemma (is_mono_suffix l (enqueue_todo l t)._1)
= is_same_refl l

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

let certificate (r:ghost_mono_ref) (t: task) (pos: nat)
= M.witnessed r (task_in_queue t pos)

// can witness that task is in queue
let get_certificate (t: task) (pos: nat)
            (r:ghost_mono_ref)
            (l:mono_list)
            (_:squash (task_in_queue t pos l))
  : //TODO: SteelAtomicUT
  stt_atomic (certificate r t pos) #Unobservable
    emp_inames
                  (M.pts_to r full_perm l)
                  (fun _ -> M.pts_to r full_perm l)
= admit()
(* witness r l _ *)


#pop-options

(* TODO: Replace *)
let alloc_M (#a:Type) (#p:Preorder.preorder a) (v:a)
  : stt_atomic (M.ref a p) #Unobservable emp_inames emp (fun r -> M.pts_to r full_perm v)
= admit()



(* 0: init queue *)
```pulse
unobservable fn create_ghost_queue_ (_: unit)
requires emp
returns res: (r: ghost_mono_ref & inv (inv_ghost_queue r))
ensures M.pts_to res._1 one_half []
{

  let r = alloc_M #_ #is_mono_suffix [];
  M.share r full_perm [];
  fold tasks_res [];
  rewrite each (half_perm full_perm) as one_half;
  fold inv_ghost_queue r;
  let i: inv (inv_ghost_queue r) = new_invariant (inv_ghost_queue r);
  let res: (r: ghost_mono_ref & inv (inv_ghost_queue r)) = Mkdtuple2 #_ #(fun r -> inv (inv_ghost_queue r)) r i;
  rewrite each r as res._1;
  res
}
```

let create_ghost_queue = create_ghost_queue_

```pulse
ghost fn add_todo_task (t: task) (l:mono_list)
  requires GR.pts_to t._1 #one_half true ** GR.pts_to t._2 #one_half false ** pts_to t._4._1 #one_half false ** GR.pts_to t._5 #one_half false
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
let task_queue: Type0 = list task
let link (l: mono_list) (q: task_queue) (c: int): prop
= (count_ongoing l == c /\ get_actual_queue l == q)

```pulse
unobservable fn add_todo_task_to_queue_alt_ (r: ghost_mono_ref) (i: inv (inv_ghost_queue r)) (t: task) (vc: int) (vq: list task)
requires (exists* l. M.pts_to r one_half l ** pure (link l vq vc))
  ** GR.pts_to t._1 #one_half true ** GR.pts_to t._2 #one_half false ** pts_to t._4 #one_half false ** GR.pts_to t._5 #one_half false
returns w: pos:nat & certificate r t pos
ensures exists* l. M.pts_to r one_half l ** pure (link l (t::vq) vc)
//(enqueue_todo l t)._1
opens (singleton i)
{
  with_invariants i {
    unfold inv_ghost_queue r;
    with l. assert M.pts_to r one_half l;
    M.gather r one_half one_half l _;
    //let p = enqueue_todo l t;
    //let pos = p._2;
    rewrite each (sum_perm one_half one_half) as full_perm;
    (* val read (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  : stt_ghost (erased a)
        (pts_to r #p n)
        (fun x -> pts_to r #p n ** pure (n == x)) *)
    let ll = (t, Todo)::l;
    //M.write r ll;
    admit()
    (*
    let w: certificate r t pos = get_certificate t pos r p._1 _;
    add_todo_task t l;
    M.share r full_perm _;
    rewrite each (half_perm full_perm) as one_half;
    fold inv_ghost_queue r;
    let res = (| pos, w |);
    res
    *)
  }
}
```

let x = ()
*)



```pulse
unobservable fn add_todo_task_to_queue_ (r: ghost_mono_ref) (i: inv (inv_ghost_queue r)) (t: task)
(l: mono_list)
requires M.pts_to r one_half l ** GR.pts_to t._1 #one_half true ** GR.pts_to t._2 #one_half false ** pts_to t._4._1 #one_half false ** GR.pts_to t._5 #one_half false
returns w: pos:nat & certificate r t pos
ensures M.pts_to r one_half (enqueue_todo l t)._1
opens (singleton i)
{
  with_invariants i {
    unfold inv_ghost_queue r;
    M.gather r one_half one_half l _;
    let p = enqueue_todo l t;
    let pos = p._2;
    rewrite each (sum_perm one_half one_half) as full_perm;
    M.write r p._1;
    let w: certificate r t pos = get_certificate t pos r p._1 _;
    add_todo_task t l;
    M.share r full_perm _;
    rewrite each (half_perm full_perm) as one_half;
    fold inv_ghost_queue r;
    let res = (| pos, w |);
    res
  }
}
```


let add_todo_task_to_queue = add_todo_task_to_queue_

// 2: Pop
```pulse
ghost fn rec pop_task_from_todo_to_ongoing
(l: mono_list{~(get_actual_queue l == [])})
requires tasks_res l
ensures tasks_res (pop_todo_task l)._2 ** 
  GR.pts_to (pop_todo_task l)._1._1 #one_half true ** GR.pts_to (pop_todo_task l)._1._2 #one_half false ** ongoing_condition (pop_todo_task l)._1
decreases l
{
  let et = L.hd l;
  let q = L.tl l;
  let p = pop_todo_task l;
  rewrite (tasks_res l) as (task_res et ** tasks_res q);
  if (et._2 = Todo) {
    unfold task_res et;
    from_todo_to_ongoing et;
    rewrite (task_res (et._1, Ongoing) ** tasks_res q) as (tasks_res (pop_todo_task l)._2);
    rewrite each et._1 as (pop_todo_task l)._1;
    ()
  }
  else {
    assert pure (get_actual_queue l == get_actual_queue (L.tl l));
    pop_task_from_todo_to_ongoing (L.tl l);
    rewrite each (pop_todo_task (L.tl l))._1 as (pop_todo_task l)._1;
    rewrite (task_res et ** tasks_res (pop_todo_task (L.tl l))._2) as (tasks_res (pop_todo_task l)._2);
    ()
  }
}
```


```pulse
unobservable fn pop_task_ghost_
(r: ghost_mono_ref) (i: inv (inv_ghost_queue r)) (l: mono_list{~(get_actual_queue l == [])})
  requires M.pts_to r one_half l 
  returns pair:(pos:nat & certificate r (pop_todo_task l)._1 pos)
  ensures M.pts_to r one_half (pop_todo_task l)._2 ** ongoing_condition (pop_todo_task l)._1 ** GR.pts_to (pop_todo_task l)._1._1 #one_half true ** GR.pts_to (pop_todo_task l)._1._2 #one_half false
  opens (singleton i)
{
  with_invariants i {
    unfold inv_ghost_queue r;
    M.gather r one_half one_half l _;
    rewrite each (sum_perm one_half one_half) as full_perm;
    let p = pop_todo_task l;
    let order_is_preserved = pop_preserves_order l;
    M.write r p._2;
    let w: certificate r p._1 p._3 = get_certificate p._1 p._3 r p._2 _;

    rewrite each p._2 as (pop_todo_task l)._2;
    pop_task_from_todo_to_ongoing l;

    M.share r full_perm _;
    rewrite each (half_perm full_perm) as one_half;
    fold inv_ghost_queue r;
    Mkdtuple2 #_ #(fun pos -> certificate r (pop_todo_task l)._1 pos) p._3 w
  }
}
```

let pop_task_ghost = pop_task_ghost_

// 3: From ongoing to todo: close_task

let rec close_task_bis_preserves_order_aux
    (t: task)
    (pos: nat)
    (l: mono_list{task_in_queue t pos l}):
    Lemma (is_same_mono_list l (close_task_bis t pos l) )
= match l with
| (t', s)::q -> if pos + 1 = L.length l then is_mono_suffix_refl q
else let q' = close_task_bis t pos q in close_task_bis_preserves_order_aux t pos q



let close_task_bis_preserves_order
    (t: task)
    (pos: nat)
    (l: mono_list{task_in_queue t pos l}):
    Lemma (is_mono_suffix l (close_task_bis t pos l) )
= close_task_bis_preserves_order_aux t pos l; from_same_to_suffix l (close_task_bis t pos l)

(* updates the *done* reference, so not ghost or unobservable *)
```pulse
atomic fn rec close_task_from_ongoing_to_done
(t: task) (pos: nat) (l: mono_list{task_in_queue t pos l})
  requires GR.pts_to t._1 #one_half false ** GR.pts_to t._2 #one_half true ** ongoing_condition t ** (exists* v. pts_to t._4._1 #one_half v)
    ** tasks_res l
  //returns et:
  ensures tasks_res (close_task_bis t pos l) ** pts_to t._4._1 #one_half true ** task_done t
  decreases l
{
  rewrite tasks_res l as (task_res (L.hd l) ** tasks_res (L.tl l));
  if (pos + 1 = L.length l)
  {
    let et = L.hd l;
    assert task_res et ** pure (et._1 == t);
    rewrite each t as et._1;

    from_ongoing_to_done et;
    rewrite (task_res (et._1, Done) ** tasks_res (L.tl l)) as tasks_res (close_task_bis t pos l);
    rewrite each et._1 as t;
    ()
  }
  else {
    assert pure (pos + 1 < L.length l);
    close_task_from_ongoing_to_done t pos (L.tl l);
    rewrite (task_res (L.hd l) ** tasks_res (close_task_bis t pos (L.tl l))) as tasks_res (close_task_bis t pos l);
    ()
  }
}
```


```pulse
atomic fn conclude_task_ (t: task) (pos: nat)
(r: ghost_mono_ref) (i: inv (inv_ghost_queue r))
// (w: certificate r t pos) Needed to prove the refinement type
(l: mono_list{task_in_queue t pos l})
  requires M.pts_to r one_half l **
    GR.pts_to t._1 #one_half false ** GR.pts_to t._2 #one_half true ** ongoing_condition t ** (exists* v. pts_to t._4._1 #one_half v)
  ensures M.pts_to r one_half (close_task_bis t pos l) ** pts_to t._4._1 #one_half true ** task_done t
  //M.pts_to r one_half (pop_todo_task l)._2 ** ongoing_condition (pop_todo_task l)._1 ** GR.pts_to (pop_todo_task l)._1._1 #one_half true ** GR.pts_to (pop_todo_task l)._1._2 #one_half false
  opens (singleton i)
{
  with_invariants i {
    unfold inv_ghost_queue r;
    M.gather r one_half one_half l _;
    rewrite each (sum_perm one_half one_half) as full_perm;
    let p = close_task_bis t pos l;
    let order_is_preserved = close_task_bis_preserves_order t pos l;
    M.write r p;

    close_task_from_ongoing_to_done t pos l;
    M.share r full_perm _;
    rewrite each (half_perm full_perm) as one_half;
    fold inv_ghost_queue r;
    ()
  }
}
```

let conclude_task = conclude_task_
(*
Needed:
0. Create ghost queue empty, invariant (with half permission)
We give back the other half

1. We add a task, get a certificate

2. We get a task, and switch it from todo to ongoing

3. We turn an ongoing task to todo

4. We claim? We create the pledges?
*)
