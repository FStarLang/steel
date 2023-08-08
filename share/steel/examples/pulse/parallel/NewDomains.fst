module NewDomains

open Steel.Memory
open Steel.ST.Effect
open Steel.ST.Util

module Lock = Pulse.Lib.SpinLock
open Pulse.Lib.Pervasives
open Pulse.Lib.Core
module HR = Pulse.Lib.HigherReference
module DI = Pulse.Lib.DisposableInvariant
module GR = Pulse.Lib.GhostReference

open FStar.List.Tot.Base

(*
assume val domain : a:Type0 -> (a -> vprop) -> Type0
// should contain (at least):
// 1. the reference where we will put the result
// 2. a lock that gives back the postcondition

assume val joinable :
  #a:Type0 -> #post:(a -> vprop) ->
  domain a post -> vprop
*)

(*
noeq
type par_env = | ParEnv : list task -> par_env
and task = | Task : (ref par_env -> stt nat emp (fun _ -> emp)) -> task
*)

//let unit_emp_stt_pure_pure a p
//  = unit -> stt a emp (fun x -> pure (p x))
  // depends negatively on par_env

(*
//TODO: Adapt
Ignoring the pure post; It can be expressed as part of the type
let maybe_sat #a (p: a -> prop) (x: option a)
  = match x with
  | None -> True
  | Some x -> p x
  *)

let unit_emp_stt_pure_pure a
  = unit -> stt a emp (fun _ -> emp)

(*
let unit_with_inv a: Type u#2 =
  pre:vprop -> inv_pre:DI.inv pre -> post:(a -> vprop) -> inv_post:(x:a -> DI.inv (post x))
  -> unit
  -> stt a (DI.active full_perm inv_pre) (fun x -> DI.active full_perm (inv_post x))
*)

let half = half_perm full_perm

// ignoring the pure post

let own_res r = (exists_ (fun v -> pts_to r half v ** (if None? v then pts_to r half v else emp)))

```pulse
fn read_own_res (#a: Type0) (r: ref (option a))
  requires own_res #a r
  returns v: option a
  ensures own_res #a r
{
  unfold (own_res r);
  let v = !r;
  fold (own_res r);
  v
}
```

// TODO: Once it is possible, we should have an SL pre and post
// TODO: Maybe add an id, such that every task is unique
let task_elem: Type u#1 = (
  a: Type0 // return type of the computation
  //& p: (a -> prop) // postcondition about the return value: Ignored
  //& (unit_with_inv a) // the computation
  & (unit_emp_stt_pure_pure a)
  & r: ref (option a) // the reference where we put the result of the computation
  & Lock.lock (own_res r)//(exists_ (fun v -> pts_to r half v ** (if None? v then pts_to r half v else emp)))
  // can a thread prove that this thing has not been done, before it finishes? Probably not
  // more ghost stuff
)
// depends negatively on par_env

#push-options "--print_universes"

//let task_queue: Type u#(174590) = not crashing
//let task_queue: Type u#(174591) = crashing
let task_queue: Type u#1 = list task_elem
// depends negatively on par_env

// Ghost stuff
// Goal: Prove that, at the end, all tasks are done (and thus all results are Some ...)
type task_status = | Todo | Ongoing | Done

let task_plus: Type u#1 = 
(
  task: task_elem
  & status: task_status
  //& post: (task._1 -> vprop)
  //& post_claimed: ref bool // needs to be ref, so it can be provably false
  //& done: option (x:task._1 & DI.inv (post x))
)

//#push-options "--warn_error -249"

let mono_list_task_plus: Type u#1 = list task_plus
// should evolve according to preorder

//let in_queue (t: task_elem) (vq: list task_elem): prop
//= mem_prop_is_affi t vq

let decrement_if_ongoing (t: task_plus) (c: int)
= if Ongoing? t._2 then c - 1 else c

(*
let good_task_plus (t: task_plus) (q: task_queue) =
  match t._2 with
  | Todo -> pure (squash (memP t._1 q)) //** pure_inv_queue q c ql
  | Ongoing -> emp//pure_inv_queue q (c - 1) ql // this task is "included" in the counter
  | Done -> (exists_ (fun v -> pts_to t._1._3 half v ** pure (Some? v))) //** pure_inv_queue q c ql
  *)

let good_task_plus (t: task_plus) (q: task_queue) =
  if Todo? t._2
    then pure (squash (memP t._1 q))
  else if Ongoing? t._2
    then emp
  else
    (exists_ (fun v -> pts_to t._1._3 half v ** pure (Some? v))) //** pure_inv_queue q c ql

let emp_list: list int = []

```pulse
fn test_rewrite_match
  (r: ref nat)
  requires pts_to r full_perm 0
  ensures pts_to r full_perm 0
{
  let l = emp_list;
  rewrite (pts_to r full_perm 0) as (`@(
    match l with
    | [] -> pts_to r full_perm 0
    | t::q -> pts_to r full_perm 1
  ));
  admit()
}
```

// the following is a vprop, because it contains half perm to res ref
(*
let rec pure_inv_queue (q: task_queue) (c: int) (l: mono_list_task_plus):
  Tot vprop (decreases l)
= match l with
| [] -> pure (c = 0)
| t::ql -> good_task_plus t q ** pure_inv_queue q (decrement_if_ongoing t c) ql
*)
let rec old_pure_inv_queue (q: task_queue) (c: int) (l: mono_list_task_plus):
  Tot vprop (decreases l)
=
if length l = 0 then pure (c = 0)
else good_task_plus (hd l) q ** old_pure_inv_queue q (decrement_if_ongoing (hd l) c) (tl l)

let rec pure_inv_queue (q: task_queue) (c: int) (l: mono_list_task_plus):
  Tot prop (decreases l)
= match l with
  | [] -> c = 0
  | tl::ql -> ((Todo? tl._2 ==> memP tl._1 q) /\ pure_inv_queue q (decrement_if_ongoing tl c) ql)

let rec pure_inv_mono t q c l
  : Lemma
  (requires pure_inv_queue q c l)
  (ensures pure_inv_queue (t::q) c l)
  (decreases l)
= match l with
  | [] -> ()
  | tl::ql -> pure_inv_mono t q (decrement_if_ongoing tl c) ql

let done_with_perm_task (t: task_plus): vprop
= (if Done? t._2
  then (exists_ (fun v -> pts_to t._1._3 half v ** pure (Some? v)))
  else emp)

```pulse
fn fold_done_task_not_done (tp: (tp:task_plus{~(Done? tp._2)}))
  requires emp
  ensures done_with_perm_task tp
{
  rewrite emp as
    ((`@(if Done? tp._2 then (exists_ (fun v -> pts_to tp._1._3 half v ** pure (Some? v)))
    else emp)));
  fold (done_with_perm_task tp)
}
```

let rec done_with_perm (l: mono_list_task_plus): vprop
=  match l with
  | [] -> emp
  | tl::ql -> done_with_perm_task tl ** done_with_perm ql

let enqueue_task_plus (t: task_plus) (l: mono_list_task_plus): mono_list_task_plus
  = t::l

```pulse
fn fold_done_task (tp: task_plus) (l:mono_list_task_plus)
  requires done_with_perm_task tp ** done_with_perm l
  ensures done_with_perm (enqueue_task_plus tp l)
{
  rewrite (done_with_perm_task tp ** done_with_perm l)
    as
  (done_with_perm (enqueue_task_plus tp l));
  ()
}
```

let inv_task_queue
  (q: HR.ref task_queue) // the task queue
  (c: ref int) // a counter of how many tasks are currently being performed
  (l: HR.ref mono_list_task_plus)
  : vprop
= (exists_ (fun vq -> exists_ (fun vc -> exists_ (fun vl ->
    HR.pts_to q full_perm vq **
    pts_to c full_perm vc **
    HR.pts_to l full_perm vl **
    done_with_perm vl **
    pure (pure_inv_queue vq vc vl)
    ))))

let par_env = (q: HR.ref task_queue & c: ref int & l: HR.ref mono_list_task_plus & Lock.lock (inv_task_queue q c l))

let get_queue (p: par_env): HR.ref task_queue
  = p._1

let get_counter (p: par_env): ref int
  = p._2

let get_mono_list (p: par_env): HR.ref mono_list_task_plus
  = p._3

let get_lock (p: par_env): Lock.lock (inv_task_queue (get_queue p) (get_counter p) (get_mono_list p))
  = p._4

let create_task_elem #a f r l: task_elem
  = (| a, f, r, l |)

assume
val higher_alloc (#a:Type) (x:a)
  : stt (HR.ref a) emp (fun r -> HR.pts_to r full_perm x)
//= admit()
//= (fun _ -> let x = HR.alloc x in return x)

assume
val higher_free (#a:Type) (r: HR.ref a)
  : stt unit (exists_ (fun v -> HR.pts_to r full_perm v)) (fun _ -> emp)

assume
val higher_read (#a:Type)
         (#p:perm)
         (#v:Ghost.erased a)
         (r:HR.ref a)
  : stt a
      (HR.pts_to r p v)
      (fun x -> HR.pts_to r p v ** pure (x == Ghost.reveal v))
      //(requires true)
//      (ensures fun x -> x == Ghost.reveal v)

assume val higher_write (#a:Type)
          (#v:Ghost.erased a)
          (r:HR.ref a)
          (x:a)
  : stt unit
      (HR.pts_to r full_perm v)
      (fun _ -> HR.pts_to r full_perm x)


let enqueue (t: task_elem) (q: task_queue): task_queue
  = t::q

```pulse
fn acquire_queue_lock
  (p: par_env)
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  requires emp
  ensures (exists vq vc vl.
    HR.pts_to (get_queue p) full_perm vq **
    pts_to (get_counter p) full_perm vc **
    HR.pts_to (get_mono_list p) full_perm vl **
    done_with_perm vl **
    pure (pure_inv_queue vq vc vl)
  )
{
  Lock.acquire (get_lock p);
  unfold (inv_task_queue (get_queue p) (get_counter p) (get_mono_list p));
  ()
}
```

```pulse
fn release_queue_lock
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  (p: par_env)
  requires (exists vq vc vl.
    HR.pts_to (get_queue p) full_perm vq **
    pts_to (get_counter p) full_perm vc **
    HR.pts_to (get_mono_list p) full_perm vl **
    done_with_perm vl **
    pure (pure_inv_queue vq vc vl)
  )
  //requires (exists vq vc. HR.pts_to (get_queue p) full_perm vq ** pts_to (get_counter p) full_perm vc)
  ensures emp
{
  fold (inv_task_queue (get_queue p) (get_counter p) (get_mono_list p));
  Lock.release (get_lock p);
  ()
}
```

let ref_ownership r: vprop
  = exists_ (fun v -> pts_to r full_perm v)


let pure_handler a
  = (res: ref (option a) & Lock.lock (own_res res)) //(exists_ (fun v -> pts_to res half v ** (if None? v then pts_to res half v else emp))))

let mk_pure_handler #a (r: ref (option a)) (l: Lock.lock (own_res r)) // (exists_ (fun v -> pts_to r full_perm v ** pure (maybe_sat p v))))
 : pure_handler a //(res: ref (option a) & Lock.lock (exists_ (fun v -> pts_to res full_perm v ** pure (maybe_sat p v))))
= (| r, l |)

(*
```pulse
fn enqueue_plus
  (t: task_elem) (q: task_queue) (c: int) (l: mono_list_task_plus)
  requires done_with_perm q c l' ** pure (pure_inv_queue l)
  returns l': mono_list_task_plus
  ensures done_with_perm (enqueue t q) c l' ** pure (pure_inv_queue l)
{
  let tp = (| t, Todo |);
  let l' = enqueue_task_plus tp l;
  assert (pure_inv_queue q c l);

  let q' = enqueue t q;

  assert (pure (squash (memP tp._1 q')));
  rewrite (pure (squash (memP tp._1 q'))) as
  (`@(if Todo? tp._2 then pure (squash (memP tp._1 q'))
    else if Ongoing? tp._2 then emp
    else (exists_ (fun v -> pts_to tp._1._3 half v ** pure (Some? v)))));
  fold (good_task_plus tp q');
  assert (good_task_plus tp q');
  assert (pure (decrement_if_ongoing tp c = c));
  assert (pure_inv_queue q c l);
  pure_inv_mono t q c l;
  rewrite (pure_inv_queue (enqueue t q) c l) as (pure_inv_queue q' (decrement_if_ongoing tp c) l);
  //assert (pure_inv_queue q' (decrement_if_ongoing tp c) q);

  assert (good_task_plus tp q' ** pure_inv_queue q' (decrement_if_ongoing tp c) l);
  fold_inv_queue tp q' c l;

  assert (pure_inv_queue q' c (enqueue_task_plus tp l));
  assert (pure_inv_queue q' c l');
  rewrite (pure_inv_queue q' c l') as (pure_inv_queue (enqueue t q) c l');
  l'
}
```
*)
  //stt_ghost mono_list_task_plus (FStar.Set.empty) (pure_inv_queue q c l) (fun l' -> pure_inv_queue (enqueue t q) c l')
  //stt mono_list_task_plus (pure_inv_queue q c l) (fun l' -> pure_inv_queue (enqueue t q) c l')

#set-options "--debug Domains --debug_level st_app --print_implicits --print_universes --print_full_names"

let typed_id a (x: a): a = x

assume val share (#a:Type0) (r:ref a) (#v:erased a) (#p:perm)
  : stt_ghost unit emp_inames
      (pts_to r p v)
      (fun _ ->
       pts_to r (half_perm p) v **
       pts_to r (half_perm p) v)

assume val gather (#a:Type0) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  : stt_ghost unit emp_inames
      (pts_to r p0 x0 ** pts_to r p1 x1)
      (fun _ -> pts_to r (sum_perm p0 p1) x0 ** pure (x0 == x1))


// should give a token
// which is a suffix of the list
// with the proof that the task has been spawn (is at the head of this list)
```pulse
fn spawn_emp'
  (#a:Type0)
  //(#post : (a -> vprop))
  //(#q: HR.ref task_queue) (#c: ref int)
  (p: par_env) // par_env'
  //(post: (a -> prop))
  //(l: Lock.lock (inv_task_queue q c))
  (f : (par_env -> unit_emp_stt_pure_pure a))
 requires emp // requires prop?
 returns r: pure_handler a //(res: ref (option a) & Lock.lock (exists_ (fun v -> pts_to res full_perm v ** pure (maybe_sat post v))))
  //Lock.lock
 ensures emp
{
  let res = Pulse.Lib.Reference.alloc #(option a) None;
  share res;
  fold (own_res res);
  let l_res = Lock.new_lock (own_res res); //(exists_ (fun v -> pts_to res full_perm v ** pure (maybe_sat post v)));
  let task = create_task_elem #a (f p) res l_res;

  acquire_queue_lock p;

  with vq. assert (HR.pts_to (get_queue p) full_perm (Ghost.reveal vq));
  with vc. assert (pts_to (get_counter p) full_perm (Ghost.reveal vc));
  with vl. assert (HR.pts_to (get_mono_list p) full_perm (Ghost.reveal vl));

  assert (done_with_perm vl ** pure (pure_inv_queue vq vc vl));

  let vc' = !(get_counter p);

  let vq' = higher_read #_ #full_perm #vq (get_queue p);
  let vq'' = enqueue task vq';
  higher_write #_ #vq (get_queue p) vq'';
  let vl' = higher_read #_ #full_perm #vl (get_mono_list p);

  let tp = (| task, Todo |);
  let vl'' = enqueue_task_plus tp vl';

  higher_write #mono_list_task_plus #vl' (get_mono_list p) vl'';

  assert (done_with_perm vl ** pure (pure_inv_queue vq vc vl));
  assert (pure (pure_inv_queue vq' vc' vl'));

  pure_inv_mono task vq vc vl;
  fold_done_task_not_done tp;
  fold_done_task tp vl';
  release_queue_lock p;
  let r = mk_pure_handler res l_res;
  r
}
```

let spawn_emp = spawn_emp'

assume val free_ref (#a:Type) (r: ref a)
 //(x:a)
  : stt unit
  (exists_ (fun v -> pts_to r full_perm v))
  (fun _ -> emp)
  


```pulse
fn join_emp'
  (#a:Type0)
  //(#post: (a -> prop))
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  //(p: par_env)
  (h: pure_handler a)
 requires emp
 returns res: a
 ensures emp
{
  let r = Pulse.Lib.Reference.alloc #(option a) None;
  while (let res = !r; None? res)
    invariant b. (exists res. pts_to r full_perm res ** pure (b == None? res))
    //** pure (maybe_sat post res))
  {
    with res. assert (pts_to r full_perm res);
    assert (pts_to r full_perm res);
    Lock.acquire h._2;
    let new_res = read_own_res h._1;// !h._1;
    //let new_res = typed_id (option a) None;
    r := new_res;
    Lock.release h._2;
    // TODO: if None? res then check whether the task we're waiting on is in the queue
    ()
  };
  let res = !r;
  free_ref r;
  Some?.v res
}
```

let join_emp = join_emp'


let len (q: task_queue): nat
= List.Tot.length q

let pop (q: task_queue{len q > 0}): task_elem & task_queue
= let t::q' = q in (t, q')

assume val assert_prop (p: prop): stt unit (pure p) (fun _ -> emp)

      (*
  a: Type0 // return type of the computation
  & p: (a -> prop) // postcondition about the return value
  & (unit_emp_stt_pure_pure a p) // the computation
  & r: ref (option a) // the reference where we put the result of the computation
  & Lock.lock (exists_ (fun v -> pts_to r full_perm v ** pure (maybe_sat p v)))
      *)

let perform_task (t: task_elem): stt (t._1) emp (fun _ -> emp)
= t._2 ()

(*
let perform_task (t: task_elem):
  (res:task._1)
= task._3 ()
*)
let get_ref_res (t: task_elem): ref (option t._1) = t._3

//let own_res r = (exists_ (fun v -> pts_to r half v ** (if None? v then pts_to r half v else emp)))

```pulse
fn unfold_and_read_own_res
  (#a: Type0) (r: ref (option a))
  requires own_res r
  returns v: option a
  ensures pts_to r half v ** `@(if None? v then pts_to r half v else emp)
{
  unfold own_res r;
  let v = !r;
  v
}
```

```pulse
fn fold_own_res_Some
(#a: Type0) (r: ref (option a)) (v: (v:option a{~(None? v)}))
  requires pts_to r half v
  ensures own_res r
{
  admit()
}
```

```pulse
fn write_res (t: task_elem) (res: t._1)
  requires emp
  ensures pts_to t._3 half (Some res)
{
  // need to check whether there is a result...
  Lock.acquire t._4;
  let v = unfold_and_read_own_res t._3;
  if (None? v) {
    rewrite `@(if None? v then pts_to t._3 half v else emp) as (pts_to t._3 half v);
    assert (pts_to t._3 half v ** pts_to t._3 half v);
    gather t._3;
    rewrite (pts_to t._3 (sum_perm half half) v) as (pts_to t._3 full_perm v);
    t._3 := Some res;
    share t._3;
    rewrite (pts_to t._3 (half_perm full_perm) (Some res)) as
      (pts_to t._3 half (Some res));
    fold_own_res_Some t._3 (Some res);
    Lock.release t._4;
    rewrite (pts_to t._3 (half_perm full_perm) (Some res)) as
      (pts_to t._3 half (Some res));
    ()
  }
  else {
    //fold (own_res t._3);
    fold_own_res_Some t._3 v;
    Lock.release t._4;
    rewrite `@(if None? v then pts_to t._3 half v else emp) as emp;
    admit() // TODO: How do we prove that this case does not happen
  }
}
```

(*

```pulse
fn decrease_counter (p: par_env)// (#q: HR.ref task_queue) (#c: ref int) (l: Lock.lock (inv_task_queue q c))
  requires emp
  ensures emp
{
  acquire_queue_lock p;
  let vc = !(get_counter p);
  (get_counter p) := vc - 1;
  release_queue_lock p;
  ()
}
```

```pulse
fn worker' //(#q: HR.ref task_queue) (#c: ref int) (l: Lock.lock (inv_task_queue q c))
  (p: par_env)
  requires emp
  ensures emp
{

  let r_working = alloc #bool true;
  
  while (let working = !r_working; working)
    invariant b. (exists w. pts_to r_working full_perm w ** pure (b == w))
  {
    acquire_queue_lock p;

    with vq. assert (HR.pts_to (get_queue p) full_perm vq);
    let vq = higher_read #_ #full_perm #vq (get_queue p);
    let vc = !(get_counter p);

    // We check whether there's a task in the queue
    if (len vq > 0) {
      // 1. pop the task and increase counter
      let pair = pop vq;
      (get_counter p) := vc + 1;
      higher_write #_ #vq (get_queue p) (pair._2);
      release_queue_lock p;
      let task = pair._1;

      // 2. perform the task
      let res = perform_task task; // (task._3) (); // Actually performing the task

      // 3. put the result in the reference
      write_res task res;

      // 4. decrease counter
      decrease_counter p;
      ()
    }
    else {
      release_queue_lock p;
      r_working := (vc > 0); // we continue working if and only if some task is still running...
      ()
    }
  };
  free_ref r_working;
  ()
}
```
let worker = worker'

let empty_task_queue: task_queue = []

let mk_par_env q c l: par_env = (| q, c, l |)

```pulse
fn init_par_env' (_: unit)
  requires emp
  returns p: par_env
  ensures emp
{
  // creating parallel env
  let work_queue = higher_alloc empty_task_queue;
  let counter = alloc 0;
  fold (inv_task_queue work_queue counter);
  assert (inv_task_queue work_queue counter);
  let lock = Lock.new_lock (inv_task_queue work_queue counter);
  let p = mk_par_env work_queue counter lock;
  p
}
```

let init_par_env = init_par_env'

let typed_id a (x:a): a = x

```pulse
fn par_block_pulse_emp' (#a: Type0)
  (#post: (a -> (prop)))
  (main_block: (par_env -> (unit_emp_stt_pure_pure a post)))
  requires emp
  returns res: a
  ensures pure (post res)
{
  let p = init_par_env ();
  // adding the main task to the queue
  let main_pure_handler = spawn_emp p post main_block;

  parallel
    requires (emp) and (emp)
    ensures (emp) and (emp)
  {
    worker p
  }
  {
    worker p
  };

  // joining main task
  let res = join_emp' #a #post main_pure_handler; // needs more typing info, from interface
  res
}
```

let par_block_pulse_emp = par_block_pulse_emp'



// -------------------------------------------------------------
// Using the previous interface to have resourceful tasks
// -------------------------------------------------------------

//let resourceful_res #a post = (x:a & Lock.lock (post x))
// question: When do I get the active vprop?
let resourceful_res #a post: Type0 = (x:a & DI.inv (post x))
//let resourceful_res_test #a post: Type0 = (x:a & post x)
// new handler
// - half perm to ref post_claimed initialized to false, allows joining to get back perm (only once)
// 

let unit_stt a pre post = (unit -> stt a pre post)

// FIXME: eta expansion makes the proof fail, but needed for now in pulse
let exec_unit_stt #a #pre #post
  (f : unit_stt a pre post)
: stt a pre (fun y -> post y)
= admit(); f ()

let mk_resourceful_res #a #post (x: a) (l: Lock.lock (post x)):
  resourceful_res post
= (| x, l |)


```pulse
fn lockify_vprops
  (#a:Type0)
  (#pre: vprop)
  (#post : (a -> vprop))
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  //(f : (unit -> (stt a pre post)))
  (f: (par_env -> unit_stt a pre post))
  (lpre: Lock.lock pre)
  (p: par_env)
  (_: unit)
  requires emp
  returns res: (resourceful_res post)
    //x:a & Lock.lock (post x))
  ensures pure (true)
{
  Lock.acquire lpre;
  // we own the pre
  let y = f p;
  let x = exec_unit_stt y;
  // we own post x
  let l = Lock.new_lock (post x);
  let res = mk_resourceful_res x l;
  res
}
```

let maybe_sat_vprop #a (p: a -> vprop) (x: option a)
  = match x with
  | None -> emp
  | Some x -> p x

let handler (#a: Type0) (post: a -> vprop)
  = pure_handler #(resourceful_res post) (fun (_: resourceful_res post) -> true)

(*
// let's get rid? of the lock
// and use invariants instead

let pure_handler #a (post: a -> prop)
  = (res: ref (option a) & Lock.lock (exists_ (fun v -> pts_to res full_perm v ** pure (maybe_sat post v))))

let resourceful_res #a post = (x:a & Lock.lock (post x))

let handler (#a: Type0) (post: a -> vprop)
  = pure_handler #(resourceful_res post) (fun (_: resourceful_res post) -> true)

handler, now:
- reference to option (result and lock with the postcondition)
- lock with full permission over this full reference

what we want:
- ref bool: done?
- ref bool: resources claimed?
- lock (invariant, really) with
- 1/2 done * 1/2 claimed * (done ==> 1/2 ref_res)
* (done && !claimed ==> post x)

The other 1/2 of done is in the end in finished...
The other 1/2 of claimed is in promise or joined (with false)
The other half of ref_res is ???
*)


```pulse
fn spawn'
  (#a:Type0)
  (#pre: vprop)
  (#post : (a -> vprop))
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  (p: par_env)
  (f : (par_env -> unit -> stt a pre post))
 requires pre
 returns r: handler post
 // let's think about what we return
 ensures emp
{
  // we create a lock for the precondition
  let lpre = Lock.new_lock pre;
  let h = spawn_emp #(resourceful_res post) p (fun _ -> true) (lockify_vprops f lpre); //(fun _ -> lockify_vprops f lpre);
  h
}
```

let spawn #a #pre #post = spawn' #a #pre #post

```pulse
fn join'
  (#a:Type0)
  (#post: (a -> vprop))
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  (h: handler post)
 requires emp
 returns res: a
 ensures post res
{
  let x = join_emp h;
  // x has type resourceful_res pot = (x:a & Lock.lock (post x))
  Lock.acquire x._2;
  x._1
}
```

let join #a #post = join' #a #post

```pulse
fn par_block_pulse' (#a: Type0) (#pre: vprop)
  (#post: (a -> vprop))
  (main_block: (par_env -> unit -> (stt a pre post)))
  requires pre
  returns res: a
  ensures post res
{
  let p = init_par_env ();
  // adding the main task to the queue
  let main_handler = spawn p main_block;

  parallel
    requires (emp) and (emp)
    ensures (emp) and (emp)
  {
    worker p
  }
  {
    worker p
  };

  // joining main task
  let res = join main_handler; // needs more typing info, from interface
  res
}
```

let par_block_pulse #a #pre #post = par_block_pulse' #a #pre #post

```pulse 
fn double (#n: nat) (r:ref nat)
  requires pts_to r full_perm n
  returns res:nat
  ensures pts_to r full_perm n ** pure (res = n + n)
{
  let vr = !r;
  let x = vr + vr;
  x
}
```

let promote_seq #a #pre #post
  (f: stt a pre post)
: par_env -> unit -> stt a pre post
= (fun _ -> fun _ -> f)

```pulse
fn add_double (#na #nb: nat) (a b: ref nat)
  (p: par_env)
  (_: unit)
  requires pts_to a full_perm na ** pts_to b full_perm nb
  returns res:nat
  ensures pts_to b full_perm nb ** pure (res = na + na + nb + nb)
{
  let aa_t = spawn p (promote_seq (double #na a));
  let bb_t = spawn p (promote_seq (double #nb b));
  let aa = join aa_t;
  let bb = join bb_t;
  let x = aa + bb;
  free_ref a;
  x
}
```

```pulse
fn par_add_double
  (a b: nat)
  requires emp
  returns r:nat
  //returns r:nat
  ensures pure (r = a + a + b + b)
{
  let a' = alloc a;
  let b' = alloc b;
  let x = par_block_pulse' (add_double #a #b a' b');
  free_ref b';
  x
}
```

let combine_posts #a #b
  (post1: a -> vprop) (post2: b -> vprop)
: (a & b) -> vprop
= (fun r -> post1 r._1 ** post2 r._2)

(*
TODO:
- Define promise list (vprop)
- Function that takes a list of elems of some type,
and returns a

e.g.,
[int, unit, nat]
f: 
*)
*)