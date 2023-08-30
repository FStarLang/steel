module NewDomains

open Steel.Memory
open Steel.ST.Effect
open Steel.ST.Util

module Lock = Pulse.Lib.SpinLock
open Pulse.Lib.Pervasives
open Pulse.Lib.Core
module HR = Pulse.Lib.HigherReference
//module DI = Pulse.Lib.DisposableInvariant
//module GR = Pulse.Lib.GhostReference



open FStar.List.Tot.Base
open GhostTaskQueue

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

#push-options "--print_universes"

(*
let unit_emp_stt_pure_pure a
  = (r: ref (option a) -> stt a (own_None r) (fun _ -> own_None r))
  // this type needs to be changed...
  // maybe take the current task (with certificate) as a parameter...
*)
type comp_task (t: task_elem) =
  unit -> stt t._1 (own_None t._2) (fun _ -> own_None t._2)

//type task_with_comp = (t:task_elem & comp_task t)

let task_queue: Type u#1 = list (t:task_elem & comp_task t)
//let task_queue: Type u#1 = list (t:task_elem & comp_task t)
//let task_plus: Type u#1 = task_with_status task_elem

#push-options "--warn_error -249"

let deadline (q: HR.ref task_queue) (c: ref int) : vprop
= exists_ (fun f ->
  exists_ (fun vq ->
  exists_ (fun vc ->
    HR.pts_to q #f vq ** pts_to c #f vc
  )))


let conditional_half
  (q: HR.ref task_queue)
  (c: ref int) (vq: task_queue) (vc: int): vprop =
  (if length vq = 0 && vc = 0 then deadline q c // we're done
  else (HR.pts_to q #one_half vq ** pts_to c #one_half vc)) // we have exclusive permission to q and c


// TODO: Support two modes?
// Once the thing is done...
let inv_task_queue
  (q: HR.ref task_queue) // the task queue
  (c: ref int) // a counter of how many tasks are currently being performed
  (r: ghost_mono_ref task_elem)
  : vprop
= (exists_ (fun vq ->
  exists_ (fun vc -> 
    HR.pts_to q #one_half vq ** pts_to c #one_half vc ** small_inv r (map dfst vq) vc **
    conditional_half q c vq vc
    //** (if length vq = 0 && vc = 0 then emp // we're done
     // else (HR.pts_to q #one_half vq ** pts_to c #one_half vc) // we have exclusive permission to q and c
    )))

let par_env = (q: HR.ref task_queue & c: ref int & r: ghost_mono_ref task_elem & Lock.lock (inv_task_queue q c r))
// & current_task r)

let current_task (p: par_env) = (t:task_elem & pos:nat & certificate p._3 t pos)

let mk_current_task (p: par_env) (t:task_elem) (pos:nat) (w:certificate p._3 t pos):
  (ct:current_task p{ct._1 == t})
= (| t, pos, w |)

let update_par_env
  #r (#t: task_elem) (#pos: nat)
  (p: par_env) (w: certificate r t pos)
= (| p._1, p._2, p._3, p._4, (| t, pos, w |) |)

let is_active #r (ct: current_task r): vprop = pts_to ct._1._2 #three_quart None

let get_queue (p: par_env): HR.ref task_queue
  = p._1

let get_counter (p: par_env): ref int
  = p._2

let get_mono_list (p: par_env): ghost_mono_ref task_elem
  = p._3

let get_lock (p: par_env): Lock.lock (inv_task_queue (get_queue p) (get_counter p) (get_mono_list p))
  = p._4

//let get_current_task (p: par_env): current_task (get_mono_list p)//Lock.lock (inv_task_queue (get_queue p) (get_counter p) (get_mono_list p))
 // = p._5

let create_task_elem #a (r: ref (option a)) (l: Lock.lock (own_res r))
: task_elem
  = (| a, r, l|)

assume
val higher_alloc (#a:Type) (x:a)
  : stt (HR.ref a) emp (fun r -> HR.pts_to r x)

assume
val higher_free (#a:Type) (r: HR.ref a)
  : stt unit (exists_ (fun v -> HR.pts_to r v)) (fun _ -> emp)

assume
val higher_read (#a:Type)
         (#p:perm)
         (#v:Ghost.erased a)
         (r:HR.ref a)
  : stt a
      (HR.pts_to r #p v)
      (fun x -> HR.pts_to r #p v ** pure (x == Ghost.reveal v))
      //(requires true)
//      (ensures fun x -> x == Ghost.reveal v)

assume val higher_write (#a:Type)
          (#v:Ghost.erased a)
          (r:HR.ref a)
          (x:a)
  : stt unit
      (HR.pts_to r v)
      (fun _ -> HR.pts_to r x)

let enqueue (t: task_elem) (c:comp_task t) (q: task_queue): task_queue
  = (|t, c|)::q

```pulse
fn acquire_queue_lock
  (p: par_env)
  requires emp
  ensures (exists vq vc.
    HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc
    ** small_inv (get_mono_list p) (map dfst vq) vc
    ** conditional_half (get_queue p) (get_counter p) vq vc
    )
{
  Lock.acquire (get_lock p);
  unfold (inv_task_queue (get_queue p) (get_counter p) (get_mono_list p));
  with vq vc. assert (HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc);
  assert (small_inv (get_mono_list p) (map dfst vq) vc);
  ()
}
```

```pulse
fn acquire_queue_lock_ongoing
  //(#t: task_elem)
  //(#pos: nat)
  (p: par_env)
  //(w:certificate (get_mono_list p) t pos)
  (ct: current_task p)
  requires is_active ct //pts_to t._2 #three_quart None
  ensures (exists vq vc.
    HR.pts_to (get_queue p) vq ** pts_to (get_counter p) vc ** small_inv (get_mono_list p) (map dfst vq) vc)
    ** is_active ct//pts_to t._2 #three_quart None
{
  acquire_queue_lock p;
  //let q = get_queue p;
  with vq. assert (HR.pts_to (get_queue p) #one_half vq);
  with vc. assert (pts_to (get_counter p) #one_half vc);
  assert (small_inv (get_mono_list p) (map dfst vq) vc);
  //let ct = get_current_task p;
  unfold is_active ct;
  prove_task_ongoing #_ #_ #None (get_mono_list p) (map dfst vq) vc ct._3;
  //rewrite (pts_to p._5._1._2 #three_quart None) as (is_active p);
  fold is_active ct;
  assert (pure (vc > 0));
  assert (small_inv (get_mono_list p) (map dfst vq) vc);
  assert (conditional_half (get_queue p) (get_counter p) vq vc);
  //unfold (conditional_half (get_queue p) (get_counter p) vq vc);
  rewrite `@(if length vq = 0 && vc = 0 then deadline (get_queue p) (get_counter p) // we're done
      else (HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc))
    as (HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc);
  assert (HR.pts_to (get_queue p) #one_half vq ** HR.pts_to (get_queue p) #one_half vq);
    //as (HR.pts_to (get_queue p) #one_half vq ** HR.pts_to (get_counter p) #one_half vc);
  //assert (small_inv (get_mono_list p) vq vc);
  HR.gather2 #_ #emp_inames (get_queue p) #vq;
  gather2 #_ #emp_inames (get_counter p) #vc;
  //assert (small_inv (get_mono_list p) vq vc);
  ()
}
```

```pulse
fn release_queue_lock
  (p: par_env)
  requires (exists vq vc.
    HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc
    ** small_inv (get_mono_list p) (map dfst vq) vc
    ** conditional_half (get_queue p) (get_counter p) vq vc
    )
  ensures emp
{
  fold (inv_task_queue (get_queue p) (get_counter p) (get_mono_list p));
  Lock.release (get_lock p);
  ()
}
```

```pulse
fn release_queue_lock_ongoing
  //(#t: task_elem)
  //(#pos: nat)
  (p: par_env)
  //(w:certificate (get_mono_list p) t pos)
  (ct: current_task p)
  requires is_active ct //pts_to t._2 #three_quart None
    ** (exists vq vc. HR.pts_to (get_queue p) vq ** pts_to (get_counter p) vc
    ** small_inv (get_mono_list p) (map dfst vq) vc)
  ensures is_active ct//pts_to t._2 #three_quart None
{
  with vq vc. assert (HR.pts_to (get_queue p) vq ** pts_to (get_counter p) vc
  ** small_inv (get_mono_list p) (map dfst vq) vc);
  share2 #_ #emp_inames (get_counter p);
  HR.share2 #_ #emp_inames (get_queue p);
  //let b: bool = (length vq = 0 && vc = 0);
  //rewrite (is_active ct) as (pts_to ct._1._2 #three_quart None);
  unfold is_active ct;
  prove_task_ongoing #_ #_ #None (get_mono_list p) (map dfst vq) vc ct._3;
  fold is_active ct;
  //rewrite (pts_to ct._1._2 #three_quart None) as (is_active ct);
  //let proof = prove_task_ongoing (get_mono_list p) vq vc w;
  rewrite 
      (HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc)
    as
      `@(if length vq = 0 && vc = 0 then deadline (get_queue p) (get_counter p) // we're done
      else (HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc));
  //fold (inv_task_queue (get_queue p) (get_counter p) (get_mono_list p));
  //rewrite (inv_task_queue (get_queue p) (get_counter p) (get_mono_list p)) as (get_lock p);
  //fold (get_lock p);
  //assert (get_lock p);// (get_queue p) (get_counter p) (get_mono_list p));
  //Lock.release (get_lock p);
  release_queue_lock p;
  ()
}
```

// the task could also be erased?
let pure_handler a (p: par_env)
  = (res: ref (option a) & Lock.lock (own_res res)
  & t: erased task_elem & pos:erased nat & erased (certificate (get_mono_list p) t pos)
 // also needed: task, pos, certificate, connection between them 
  )

let mk_pure_handler #a
  (#t: task_elem) (#pos: erased nat)
  (p: par_env)
  (r: ref (option a)) (l: Lock.lock (own_res r))
  (w: erased (certificate (get_mono_list p) t pos))
 : pure_handler a p //(res: ref (option a) & Lock.lock (exists_ (fun v -> pts_to res full_perm v ** pure (maybe_sat p v))))
= (| r, l, hide t, pos, w |)

#set-options "--debug Domains --debug_level st_app --print_implicits --print_universes --print_full_names"

let typed_id a (x: a): a = x

```pulse
ghost
fn share_quarter
  (#a: Type0) (r: ref a)
requires pts_to r v
ensures pts_to r #one_quart v ** pts_to r #three_quart v
{
  share2 #_ #emp_inames r;
  share #_ #emp_inames r;
  rewrite (pts_to r #(half_perm one_half) v) as (pts_to r #one_quart v);
  gather #_ #emp_inames r #v #v #one_half #(half_perm one_half);
  rewrite (pts_to r #(sum_perm one_half (half_perm one_half)) v) as (pts_to r #three_quart v);
  ()
}
```

// assuming because of universe polymorphism
assume val
stt_return #a (x:a): stt a emp (fun y -> pure (x == y))

// need to impose relationship between t and ct
assume val coerce_unit_stt #a #p (ct: erased (current_task p)) (t: task_elem)
  (comp: (unit -> stt a (is_active ct) (fun _ -> is_active ct)))
: unit -> stt t._1 (own_None t._2) (fun _ -> own_None t._2)



```pulse
fn spawn_emp'
  (#a:Type0)
  //(#post : (a -> vprop))
  //(#q: HR.ref task_queue) (#c: ref int)
  (p: par_env) // par_env'
  //(post: (a -> prop))
  //(l: Lock.lock (inv_task_queue q c))
  //(f : funct a) //(p':par_env -> unit_emp_stt_pure_pure a p'._5._2))
  //(f: (p:par_env -> unit -> stt a (is_active p) (fun _ -> is_active p)))
  (ct: current_task p)
  //unit -> stt t._1 (own_None t._2) (fun _ -> own_None t._2)
  (f: (par_env -> ct:erased (current_task p) -> unit -> stt a (is_active ct) (fun _ -> is_active ct)))

  // type comp_task (t: task_elem) =
  //unit -> stt t._1 (own_None t._2) (fun _ -> own_None t._2)

 requires is_active ct // requires prop?
 returns r: pure_handler a p //(res: ref (option a) & Lock.lock (exists_ (fun v -> pts_to res full_perm v ** pure (maybe_sat post v))))
  //Lock.lock
 ensures is_active ct
 // should return a promise here?
{
  let res : ref (option a) = Pulse.Lib.Reference.alloc #(option a) None;
  share_quarter res;
  //fold is_active 
  //share res;
  fold (own_res res);
  let l_res = Lock.new_lock (own_res res); //(exists_ (fun v -> pts_to res full_perm v ** pure (maybe_sat post v)));

  // needs new environment
  // cyclic dependency...

  //let fp = typed_id (unit_emp_stt_pure_pure a (get_current_task p)._1._2) (f p);

  let task: task_elem = stt_return (create_task_elem #a res l_res);// fp;

  acquire_queue_lock_ongoing p ct;

  with vq. assert (HR.pts_to (get_queue p) (Ghost.reveal vq));
  with vc. assert (pts_to (get_counter p) (Ghost.reveal vc));
  assert (HR.pts_to (get_queue p) vq ** pts_to (get_counter p) vc
    ** small_inv (get_mono_list p) (map dfst vq) vc
    ** is_active ct);

  // adding the task to the ghost queue
  rewrite (pts_to res #three_quart None) as (pts_to task._2 #three_quart None);
  assert (small_inv (get_mono_list p) (map dfst vq) vc);
  let v_tasks = hide (map dfst vq);
  rewrite (small_inv (get_mono_list p) (map dfst vq) vc)
    as (small_inv (get_mono_list p) v_tasks vc);
  let pos_certif: erased (pos:nat & certificate (get_mono_list p) task pos)
    = spawn_task_ghost (get_mono_list p) v_tasks vc task;
  assert (small_inv (get_mono_list p) (task::v_tasks) vc);

  let certif: erased (certificate (get_mono_list p) task ((reveal pos_certif)._1)) =
    hide ((reveal pos_certif)._2);
  let ct': erased (current_task p) = hide (mk_current_task p task ((reveal pos_certif)._1) certif); 


  let comp_aux: (unit -> stt a (is_active ct') (fun _ -> is_active ct')) = f p ct';
  let comp: comp_task task = coerce_unit_stt ct' task comp_aux;

  let vc' = !(get_counter p);
  let vq' = higher_read #_ #full_perm #vq (get_queue p);
  let vq'': task_queue = enqueue task comp vq';
  higher_write #_ #vq (get_queue p) vq'';

  rewrite (small_inv (get_mono_list p) (task::v_tasks) vc)
    as (small_inv (get_mono_list p) (map dfst vq'') vc);
  
  assert (HR.pts_to (get_queue p) vq'');
  assert (exists vc vq. HR.pts_to (get_queue p) vq ** small_inv (get_mono_list p) (map dfst vq) vc
   ** pts_to (get_counter p) vc);
  release_queue_lock_ongoing p ct;

  let r = mk_pure_handler p res l_res certif;
  r
}
```

let spawn_emp = spawn_emp'

assume val free_ref (#a:Type) (r: ref a)
 //(x:a)
  : stt unit
  (exists_ (fun v -> pts_to r #full_perm v))
  (fun _ -> emp)
  

```pulse
fn join_emp'
  (#a:Type0)
  //(#post: (a -> prop))
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  (p: par_env)
  (h: pure_handler a p)
 requires emp
 returns res: a
 ensures emp
{
  let r = Pulse.Lib.Reference.alloc #(option a) None;
  while (let res = !r; None? res)
    invariant b. (exists res. pts_to r res ** pure (b == None? res))
    //** pure (maybe_sat post res))
  {
    with res. assert (pts_to r res);
    assert (pts_to r res);
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

let pop (q: task_queue{len q > 0}): (t:task_elem & comp_task t) & task_queue
= (hd q, tl q) //let t::q' = q in (t, q')

assume val assert_prop (p: prop): stt unit (pure p) (fun _ -> emp)

let perform_task #t (comp: comp_task t): stt (t._1) (own_None t._2) (fun _ -> own_None t._2)
= comp ()

(*
let perform_task (t: task_elem):
  (res:task._1)
= task._3 ()
*)
let get_ref_res (t: task_elem): ref (option t._1) = t._2

//let own_res r = (exists_ (fun v -> pts_to r half v ** (if None? v then pts_to r half v else emp)))

```pulse
fn unfold_and_read_own_res
  (#a: Type0) (r: ref (option a))
  requires own_res r
  returns v: option a
  ensures pts_to r #one_quart v 
{
  unfold own_res r;
  let v = !r;
  v
}
```

```pulse
fn fold_own_res_Some
(#a: Type0) (r: ref (option a)) (v: (v:option a{~(None? v)}))
  requires pts_to r #one_quart v
  ensures own_res r
{
  fold (own_res r)
}
```

```pulse
ghost
fn gather_quarter
  (#a: Type0) (r: ref a)
requires pts_to r #one_quart v1 ** pts_to r #three_quart v2
ensures pts_to r v2 ** pure (v1 == v2)
{
  gather #_ #emp_inames r #v1 #v2 #one_quart #three_quart;
  rewrite (pts_to r #(sum_perm one_quart three_quart) v1) as (pts_to r v2);
  ()
}
```

```pulse
fn write_res (t: task_elem) (res: t._1)
  requires pts_to t._2 #three_quart None // we got that from the todo part
  ensures pts_to t._2 #three_quart (Some res)
{
  //assert (pts_to t._3 half None);
  Lock.acquire t._3;
  let v = unfold_and_read_own_res t._2;
  assert (pts_to t._2 #one_quart v ** pts_to t._2 #three_quart None);
  gather_quarter t._2;
  t._2 := Some res;
  share_quarter t._2;
  fold_own_res_Some t._2 (Some res);
  Lock.release t._3
}
```

// need to remove one ongoing task now!
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
fn update_task_ongoing
  (task: task_elem) (vq:(vq:task_queue{len vq > 0})) (vc: int) (vl: mono_list_task_plus)
  requires tasks_res_own vl ** pure (pure_inv_queue vq vc vl)
  returns vl': mono_list_task_plus
  ensures tasks_res_own vl' ** pts_to task._3 half None
    ** pure (pure_inv_queue (tl vq) (vc + 1) vl')
{
  admit()
}
```

(*
let rec pure_inv_queue (q: task_queue) (c: int) (l: mono_list_task_plus):
  Tot prop (decreases l)
= match l with
  | [] -> c = 0
  | tl::ql -> ((Todo? tl._2 ==> memP tl._1 q) /\ pure_inv_queue q (decrement_if_ongoing tl c) ql)
*)

(*
      // 1. We need to remove the task from vl
      // such that we get back 1/2 permission to the res
      // FROM
      assert (tasks_res_own vl);
      assert (pure (pure_inv_queue vq vc vl));
      // TO
      // vl' = vl where the status of "task" has gone from Todo to Ongoing
      assert (tasks_res_own vl' ** pts_to task._3 half None);
      assert (pure (pure_inv_queue (tl vq) (vc + 1) vl'));
      *)

(*
This function decrements the counter,
and sets the task (which is provably ongoing) to "done" in the ghost list
*)
```pulse
fn declare_task_done (p: par_env) (task: task_elem) (res: task._1)
  requires pts_to task._3 half (Some res)
  ensures emp
{
  acquire_queue_lock p;

  // getting a hold of the three things
  with vq. assert (HR.pts_to (get_queue p) full_perm (Ghost.reveal vq));
  let vq = higher_read #_ #full_perm #vq (get_queue p);
  let vc = !(get_counter p);
  with vl. assert (HR.pts_to (get_mono_list p) full_perm (Ghost.reveal vl));
  let vl = higher_read #_ #full_perm #vl (get_mono_list p);

  (get_counter p) := vc - 1;
  //higher_write #_ #vq (get_queue p) (pair._2);
  //let task = pair._1;
  assert (HR.pts_to (get_queue p) full_perm vq **
    pts_to (get_counter p) full_perm (vc - 1) **
    HR.pts_to (get_mono_list p) full_perm vl);
  //let vl' = update_task_ongoing task vq vc vl;
  //assert (tasks_res_own vl' ** pts_to task._3 half None ** pure (pure_inv_queue (tl vq) (vc + 1) vl'));
  //assert (tasks_res_own vl' ** pts_to task._3 half None ** pure (pure_inv_queue pair._2 (vc + 1) vl'));
  let vl' = vl;
  higher_write #_ #vl (get_mono_list p) vl';




  // we also have a witness that the task was ongoing
  // 4. decrease counter
  // and declare task "done"
  //decrease_counter p;
  // we can prove that this task is still ongoing, because
  // 1. we have 1/2 permission
  // 2. the lock owns the remaining half permission
  // 3. we know task is in the list (monotonicity)
  // 4. the cases todo and done would give us 1/2 more permission, resulting in an inconsistency
  admit()
  //release_queue_lock p;
}
```
*)
```pulse
ghost
fn duplicate_deadline
(q: HR.ref task_queue) (c: ref int)
requires deadline q c
ensures deadline q c ** deadline q c
{
  unfold deadline q c;
  with f vq vc. assert (HR.pts_to q #f vq ** pts_to c #f vc);
  HR.share #_ #emp_inames q;
  share #_ #emp_inames c;
  assert ((HR.pts_to q #(half_perm f) vq ** pts_to c #(half_perm f) vc)
    ** (HR.pts_to q #(half_perm f) vq ** pts_to c #(half_perm f) vc));
  fold deadline q c;
  fold deadline q c;
  ()
}
```

```pulse
ghost
fn combine_deadline
(q: HR.ref task_queue) (c: ref int)
requires deadline q c ** deadline q c
ensures deadline q c
{
  unfold deadline q c;
  with f1 vq vc. assert (HR.pts_to q #f1 vq ** pts_to c #f1 vc);
  unfold deadline q c;
  with f2 vq' vc'. assert (HR.pts_to q #f1 vq ** pts_to c #f1 vc ** 
    HR.pts_to q #f2 vq' ** pts_to c #f2 vc');
  HR.gather #_ #emp_inames q #vq #vq' #f1 #f2;
  gather #_ #emp_inames c #vc #vc' #f1 #f2;

  assert (HR.pts_to q #(sum_perm f1 f2) vq' ** pts_to c #(sum_perm f1 f2) vc');
  fold deadline q c;
  ()
}
```




```pulse
ghost fn
rewrite_conditional_maybe_end
(p: par_env) 
(vq: task_queue) (vc: int)
requires HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc
ensures conditional_half (get_queue p) (get_counter p) vq vc
  ** `@(if length vq = 0 && vc = 0 then deadline (get_queue p) (get_counter p) else emp)
{
  if (length vq = 0 && vc = 0)
  {
    assert (HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc);
    intro_exists (fun vc -> HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc) vc;
    intro_exists (fun vq -> exists_ (fun vc -> HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc)) vq;
    intro_exists (fun f -> exists_ (fun vq -> exists_ (fun vc -> HR.pts_to (get_queue p) #f vq ** pts_to (get_counter p) #f vc))) one_half;
    fold (deadline (get_queue p) (get_counter p));
    duplicate_deadline(get_queue p) (get_counter p);
    rewrite (deadline (get_queue p) (get_counter p))
      as (conditional_half (get_queue p) (get_counter p) vq vc);
    rewrite (deadline (get_queue p) (get_counter p))
      as `@(if length vq = 0 && vc = 0 then deadline (get_queue p) (get_counter p) else emp);
    ()
  }
  else {
    rewrite (HR.pts_to (get_queue p) #one_half vq ** pts_to (get_counter p) #one_half vc)
      as (conditional_half (get_queue p) (get_counter p) vq vc);
    rewrite emp
      as `@(if length vq = 0 && vc = 0 then deadline (get_queue p) (get_counter p) else emp);
    ()
  }
}
```




assume val assume_prop (p: prop): stt unit emp (fun () -> pure p)
assume val free_certificate r t pos : certificate r t pos

assume val drop (p: vprop): stt_ghost unit emp_inames p (fun () -> emp)

let deadline_if (b: bool) (p: par_env): vprop
  = if b then deadline (get_queue p) (get_counter p) else emp

let worker_inv r_working p
= (exists_ (fun w -> pts_to r_working #one_half w ** deadline_if (not w) p))

```pulse
fn worker' //(#q: HR.ref task_queue) (#c: ref int) (l: Lock.lock (inv_task_queue q c))
  (p: par_env)
  requires emp
  ensures deadline (get_queue p) (get_counter p)
{

  let r_working = alloc #bool true;
  share2 #_ #emp_inames r_working;
  // needed to write an invariant that can be verified automatically
  rewrite emp as (deadline_if (not true) p);
  intro_exists (fun w -> pts_to r_working #one_half w ** deadline_if (not w) p) true;
  fold (worker_inv r_working p);
  while (let working = !r_working; working)
    invariant b. (exists w. pts_to r_working #one_half w ** pure (b == w)
    ** worker_inv r_working p)
  {
    acquire_queue_lock p;
    with gvq gvc. assert (
      HR.pts_to (get_queue p) #one_half gvq ** pts_to (get_counter p) #one_half gvc
      ** small_inv (get_mono_list p) (map dfst gvq) gvc
      ** conditional_half (get_queue p) (get_counter p) gvq gvc
    );

    //assert (small_inv (get_mono_list p) (map dfst ghost_vq) vc);

    let vq = higher_read #_ #one_half #gvq (get_queue p);
    let vc = !(get_counter p);

    // We check whether there's a task in the queue
    if (len vq > 0) {

      // we then have full permission to everything!
      rewrite (conditional_half (get_queue p) (get_counter p) gvq gvc)
          as (HR.pts_to (get_queue p) #one_half gvq ** pts_to (get_counter p) #one_half gvc);
      HR.gather2 #_ #emp_inames (get_queue p);
      gather2 #_ #emp_inames (get_counter p);

      // 1. pop the task and increase counter
      let pair = stt_return (pop vq);
      (get_counter p) := vc + 1;
      higher_write #_ #vq (get_queue p) (pair._2);
      let task = stt_return (pair._1._1);
      let comp: comp_task task = pair._1._2;
      assert (HR.pts_to (get_queue p) (tl gvq) **
        pts_to (get_counter p) (vc + 1));
        (*
      assert (small_inv (get_mono_list p) (map dfst gvq) gvc);
      assert (pure (task == dfst (hd gvq)));
      assert (pure (task == hd (map dfst gvq)));
      assert (pure (map dfst (tl gvq) == tl (map dfst gvq)));
      assert (pure (len gvq > 0));
      assert (pure (map dfst gvq == task::map dfst (tl gvq)));
      *)
      assert (pure (map dfst gvq == task::(map dfst (tl gvq))));
      rewrite (small_inv (get_mono_list p) (map dfst gvq) gvc)
        as (small_inv (get_mono_list p) (task::map dfst (tl gvq)) gvc);
      pop_task_ghost (get_mono_list p) task (map dfst (tl gvq)) gvc;
      assert (small_inv (get_mono_list p) (map dfst (tl gvq)) (gvc + 1));

      HR.share2 #_ #emp_inames (get_queue p);
      share2 #_ #emp_inames (get_counter p);
      assert (HR.pts_to (get_queue p) #one_half (tl gvq) ** pts_to (get_counter p) #one_half (gvc + 1));
      assume_prop (gvc >= 0); // can be derived from small_inv
      rewrite (HR.pts_to (get_queue p) #one_half (tl gvq) ** pts_to (get_counter p) #one_half (gvc + 1))
        as
        `@(
          if length (tl gvq) = 0 && gvc + 1 = 0 then deadline (get_queue p) (get_counter p) // we're done
          else (HR.pts_to (get_queue p) #one_half (tl gvq) ** pts_to (get_counter p) #one_half (gvc + 1)) // we have exclusive permission to q and c
        );
      fold (conditional_half (get_queue p) (get_counter p) (tl gvq) (gvc + 1));

      assert (
        HR.pts_to (get_queue p) #one_half (tl gvq) ** pts_to (get_counter p) #one_half (gvc + 1)
        ** small_inv (get_mono_list p) (map dfst (tl gvq)) (gvc + 1)
        ** conditional_half (get_queue p) (get_counter p) (tl gvq) (gvc + 1)
      );
      release_queue_lock p;

      // 2. perform the task
      assert (pts_to task._2 #three_quart None);
      rewrite (pts_to task._2 #three_quart None) as (own_None task._2);
      let res: task._1 = perform_task comp; // (task._3) (); // Actually performing the task
      rewrite (own_None task._2) as (pts_to task._2 #three_quart None);

      // 3. put the result in the reference
      write_res task res;
      assert (pts_to task._2 #three_quart (Some res));
      
      // 4. Conclude the task
      // TODO:
      let certif: erased (certificate (get_mono_list p) task 0)
        = hide (free_certificate (get_mono_list p) task 0);

      acquire_queue_lock p;
      with gvq gvc. assert (
        HR.pts_to (get_queue p) #one_half gvq ** pts_to (get_counter p) #one_half gvc
        ** small_inv (get_mono_list p) (map dfst gvq) gvc
        ** conditional_half (get_queue p) (get_counter p) gvq gvc
      );

      prove_task_ongoing #_ #_ #(Some res) (get_mono_list p) (map dfst gvq) gvc certif;

      // decrementing counter
      rewrite (conditional_half (get_queue p) (get_counter p) gvq gvc)
          as (HR.pts_to (get_queue p) #one_half gvq ** pts_to (get_counter p) #one_half gvc);
      gather2 #_ #emp_inames (get_counter p);
      let vc = !(get_counter p);
      assert (pts_to (get_counter p) gvc);
      (get_counter p) := vc - 1;
      assert (pts_to (get_counter p) (gvc - 1));
      share2 #_ #emp_inames (get_counter p);

      conclude_task_ghost (get_mono_list p) (map dfst gvq) gvc res certif;
      assert (small_inv (get_mono_list p) (map dfst gvq) (gvc - 1));

      rewrite_conditional_maybe_end p gvq (gvc - 1);
      // if finished, we have the deadline
      // should be wildcard permission instead of emp, and we keep it

      assert (conditional_half (get_queue p) (get_counter p) gvq (gvc - 1)
      ** `@(if length gvq = 0 && gvc - 1 = 0 then deadline (get_queue p) (get_counter p) else emp));

      (* We could stop here and not drop the resource, would be more efficient. *)
      drop (if length gvq = 0 && gvc - 1 = 0 then deadline (get_queue p) (get_counter p) else emp);

      release_queue_lock p;
      ()
    }
    else {
      if (vc = 0) {
        // we're done
        rewrite (conditional_half (get_queue p) (get_counter p) gvq gvc)
          as (deadline (get_queue p) (get_counter p));
        duplicate_deadline (get_queue p) (get_counter p);
        rewrite (deadline (get_queue p) (get_counter p))
          as (conditional_half (get_queue p) (get_counter p) gvq gvc);

        assert (
          HR.pts_to (get_queue p) #one_half gvq ** pts_to (get_counter p) #one_half gvc
          ** small_inv (get_mono_list p) (map dfst gvq) gvc
          ** conditional_half (get_queue p) (get_counter p) gvq gvc
        );

        release_queue_lock p;

        // stoping the loop, and putting the deadline in the invariant
        unfold worker_inv r_working p;
        with w. assert (pts_to r_working #one_half w ** deadline_if (not w) p);
        pts_to_injective_eq #_ #one_half #one_half #w #true r_working;

        rewrite (deadline_if (not w) p) as emp;
        //assert (deadline_if false p);
        //rewrite (dead)
        gather2 #_ #emp_inames r_working;
        r_working := false;
        share2 #_ #emp_inames r_working;
        rewrite (deadline (get_queue p) (get_counter p)) as (deadline_if (not false) p);
        intro_exists (fun w -> pts_to r_working #one_half w ** deadline_if (not w) p) false;
        fold worker_inv r_working p;
        ()
      }
      else {
        assert (
          HR.pts_to (get_queue p) #one_half gvq ** pts_to (get_counter p) #one_half gvc
          ** small_inv (get_mono_list p) (map dfst gvq) gvc
          ** conditional_half (get_queue p) (get_counter p) gvq gvc
        );
        release_queue_lock p;
        ()
      }
    }
  };

  unfold worker_inv r_working p;
  with w. assert (pts_to r_working #one_half w ** deadline_if (not w) p);
  pts_to_injective_eq #_ #one_half #one_half #w #false r_working;
  rewrite (deadline_if (not w) p) as (deadline (get_queue p) (get_counter p));
  gather2 #_ #emp_inames r_working;
 
  free_ref r_working;
  ()
}
```
(*

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