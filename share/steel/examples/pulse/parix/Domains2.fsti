module Domains2

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock

val promise (f:vprop) (v:vprop) : vprop

(* Anything that holds now holds in the future too. *)
val return_promise (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames v (fun _ -> promise f v)
  
  
val make_promise (f:vprop) (v1:vprop) (v2:vprop)
  (k : unit -> stt_ghost unit emp_inames (f ** v1) (fun _ -> v2))
  : stt_ghost unit emp_inames v1 (fun _ -> promise f v2)

(* If v1 will hold in the future, and if we can in the future make a
promise that v2 will hold given v1, then we can promise v2 with the
same deadline. *)
val bind_promise (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop) // any better way to propagate context?
        (k : unit -> stt_ghost unit emp_inames (extra ** v1) (fun () -> promise f v2))
  : stt_ghost unit emp_inames (promise f v1 ** extra) (fun () -> promise f v2)

// Hmmmm.. does this make sense? Maybe this is just a task
// val promise_handle (f:vprop) (v:vprop) : Type0
// val wait_promise (#f:vprop) (#v:vprop)
//   (h : promise_handle f v)
//   : stt unit (promise f v) (fun _ -> 

(* We can define join_promise (NB: very brittle to write this in plain stt *)
let join_promise (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (promise f v1 ** promise f v2)
              (fun () -> promise f (v1 ** v2))
  = bind_promise (promise f v2) (fun () ->
    bind_promise v1 (fun () ->
    return_promise f (v1 ** v2)))
    
let rewrite_promise (#f:vprop) (v1 : vprop) (v2 : vprop)
  (k : unit -> stt_ghost unit emp_inames v1 (fun _ -> v2))
  : stt_ghost unit
              emp_inames
              (promise f v1)
              (fun _ -> promise f v2)
= bind_sttg
    (rewrite (promise f v1) (promise f v1 ** emp)
       (vprop_equiv_trans _ _ _
         (vprop_equiv_sym _ _ (vprop_equiv_unit (promise f v1)))
         (vprop_equiv_comm _ _)))
    (fun () ->
      bind_promise #_ #v1 #_ emp (fun () ->
        bind_sttg (rewrite (emp ** v1) v1 (vprop_equiv_unit v1)) (fun () ->
        bind_sttg (k ())
          (fun () -> return_promise f v2)))
    )

val redeem_promise (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames (promise f v ** f) (fun () -> v ** f)


// ```pulse
// fn join_promise_pulse (#f:vprop) (v1:vprop) (v2:vprop)
//   (p1 : promise f v1)
//   (p2 : promise f v2)
//   requires active p1 ** active p2
//   returns p : promise f (v1 ** v2)
//   ensures active p
// {
//   admit()
// }
// ```

let task_result_cell (a:Type0)
  : Type0
  = ref (option a)

let task_done (#a:Type0) (f: perm) (t : task_result_cell a)
  : vprop
  = exists_ (fun v -> pts_to t #(half_perm f) (Some v))
  
  
let task_lock_vprop (#a:Type0) (cell : task_result_cell a) (post : a -> vprop)
  : vprop
  = exists_ (fun v -> pts_to cell #(half_perm full_perm) v **
                      (if Some? v then post (Some?.v v) else emp))
 
noeq
type task (a:Type0) (post:_) = {
  rescell : task_result_cell a;
  lk : lock (task_lock_vprop rescell post);
}

let task_active (#a:Type0) (#post:_) (t : task a post)
  : vprop
  = promise (task_done full_perm t.rescell) (exists_ (fun v -> pts_to t.rescell #(half_perm full_perm) (Some v) ** post v))

// TODO: implement this for non-ghost references
val share (#a:Type0) (r:ref a) (#v:erased a) (#p:perm)
  : Pulse.Lib.Core.stt_ghost unit
      emp_inames
      (pts_to r #p v)
      (fun _ ->
       pts_to r #(half_perm p) v **
       pts_to r #(half_perm p) v)
       
val gather (#a:Type0) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  : Pulse.Lib.Core.stt_ghost unit emp_inames
      (pts_to r #p0 x0 ** pts_to r #p1 x1)
      (fun _ -> pts_to r #(sum_perm p0 p1) x0 ** pure (x0 == x1))

let p12 = half_perm full_perm

// Phony
val drop (v:vprop) : Pulse.Lib.Core.stt_ghost unit emp_inames v (fun _ -> emp)

#set-options "--print_implicits --print_universes"

// fake version with a non-ghost body
val make_promise_phony (f:vprop) (v1:vprop) (v2:vprop)
  (k : unit -> stt unit (f ** v1) (fun _ -> v2))
  : Pulse.Lib.Core.stt_ghost unit emp_inames v1 (fun _ -> promise f v2)

// val awaited : #a:Type -> #post:_ -> task a post -> vprop
```pulse
fn async0
  (#a:Type0)
  (#pre #post : _)
  (f : (unit -> stt a pre post))
  requires pre
  returns t : task a post
  ensures task_active t
{
  let v : option u#0 a = None #a;
  let rescell : ref (option u#0 a) = alloc #(option a) v;
  share rescell #v #full_perm;
  rewrite (pts_to rescell #(half_perm full_perm) v ** emp)
       as (pts_to rescell #(half_perm full_perm) v ** `@(if Some? v then post (Some?.v v) else emp));
  fold (task_lock_vprop rescell post);
  let lk = new_lock (task_lock_vprop rescell post);
  let task = Mktask rescell lk;
  
  (* These will be lost by forking the task, which we don't do yet *)
  drop pre;
  drop (pts_to rescell #(half_perm full_perm) v);

  make_promise_phony
    (task_done full_perm task.rescell)
    emp
    (exists_ (fun v -> pts_to task.rescell #(half_perm full_perm) (Some v) ** post v))
    (fun () -> magic ()); // TODO: hoist this and write it in Pulse (should be acquire+gather+release, and proof steps)
  fold (task_active task);
  task
}
```

val await0
  (#a #post : _)
  (t : task a post)
  : stt unit (task_active t) (fun () -> task_done full_perm t.rescell ** task_active t)

#set-options "--admit_smt_queries true"

```pulse
fn get_value_and_post0
  (#a:Type0)
  (#post : _)
  (t : task a post)
  requires (task_done full_perm t.rescell ** task_active t)
  returns x : a
  ensures task_done full_perm t.rescell ** post x
{
 unfold (task_active t);
 redeem_promise (task_done full_perm t.rescell) (exists_ (fun (v:a) -> pts_to t.rescell #(half_perm full_perm) (Some v) ** post v));
 with v. assert (pts_to t.rescell #(half_perm full_perm) (Some v) ** post v);
 let r : option u#0 a = !t.rescell;
 assert (pts_to t.rescell #(half_perm full_perm) r);
 let vvv : a = (match r with Some v -> v);
 assert (pure (reveal u#0 #a v == vvv));
 assert (post (reveal u#0 #a v));
 rewrite (post (reveal u#0 #a v))
      as (post vvv);
//  assert (post (hide vvv));
//  assert (pts_to t.rescell #(half_perm full_perm) (Some vvv));
 drop (pts_to t.rescell #(half_perm full_perm) (Some vvv));
 vvv
}
```

let async
  (#a #pre #post : _)
  (f : unit -> stt a pre post)
  : stt (task a post) pre (fun t -> task_active t)
= async0 f

let await_share
  (#a:Type0)
  (#post : _)
  (t : task a post)
  : stt a (task_active t) (fun x -> task_done full_perm t.rescell ** post x)
= bind_stt (await0 t) (fun () ->
  get_value_and_post0 t)

let await
  (#a:Type0)
  (#post : _)
  (t : task a post)
  : stt a (task_active t) (fun x -> post x)
= await_share t

```pulse
fn mock_http_req (cb : (string -> stt int emp (fun _ -> emp)))
  requires emp
  returns _:int
  ensures emp
{
  let t1 = async (fun () -> cb "/index.html");
  let t2 = async (fun () -> cb "/whatever");
  let v1 = await t1;
  let v2 = await t2;
  let v = v1+v2;
  v
}
```

```pulse
fn mock_http_req2_retasync (cb : (string -> stt int emp (fun _ -> emp)))
  requires emp
  returns r:(task int (fun _ -> emp))
  ensures task_active r
{
  let t1 = async (fun () -> cb "/index.html");
  let t2 = async (fun () -> cb "/whatever");
  assert (task_active t2);
  let v1 = await t1;
  t2
}
```

val pool : Type0
val pool_alive : pool -> vprop
val pool_done : pool -> vprop

val setup_pool (n:nat)
  : stt pool emp (fun p -> pool_alive p)

val spawn
  (#pre #post : _)
  (p:pool) (f : unit -> stt unit pre (fun _ -> post))
  : stt unit (pool_alive p ** pre) (fun prom -> pool_alive p ** promise (pool_done p) post)

val teardown_pool
  (p:pool)
  : stt unit (pool_alive p) (fun _ -> pool_done p)

val qsv : nat -> vprop
val qsc : n:nat -> stt unit emp (fun _ -> qsv n)

```pulse
fn qs (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  spawn p (fun () -> qsc 1);
  spawn p (fun () -> qsc 2);
  spawn p (fun () -> qsc 3);
  spawn p (fun () -> qsc 4);
  teardown_pool p;
  redeem_promise (pool_done p) (qsv 1);
  redeem_promise (pool_done p) (qsv 2);
  redeem_promise (pool_done p) (qsv 3);
  redeem_promise (pool_done p) (qsv 4);
  drop (pool_done p);
  ()
}
```
