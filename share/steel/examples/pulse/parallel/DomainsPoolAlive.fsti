module DomainsPoolAlive

open Pulse.Lib.Pervasives
module Lock = Pulse.Lib.SpinLock
module HR = Pulse.Lib.HigherReference
module M = Pulse.Lib.GhostMonotonicHigherReference

module GR = Pulse.Lib.GhostReference

open SingleGhostTask
open GhostTaskQueue

(* Pool: ghost_mono_ref, counter, task queue, lock, invariant... *)

let task_queue: Type0 = list task

(* also ghost queue? *)
val mono_queue_ref: Type0
val mono_queue: Type0 (* not 0? *)

let link (l: mono_list) (q: task_queue) (c: int): prop
= (count_ongoing l == c /\ get_actual_queue l == q)


let if_then_else (b: bool) (thn: vprop) (els: vprop): vprop
= if b then thn else els

let lock_thn (l: mono_list) q c: vprop
= (exists* vq vc. pts_to q vq ** pts_to c vc ** pure (link l vq vc))

let lock_els l status_pool: vprop
= (pure (link l [] 0) ** (exists* f1. pts_to status_pool #f1 false))
(* maybe we'll need some permission to the ghost_mono_ref? maybe not *)


let lock_pool
  (status_pool: ref bool)
  (q: ref task_queue)
  (c: ref int)
  (r: ghost_mono_ref)
: vprop
= (exists* sp l. pts_to status_pool #one_half sp ** M.pts_to r one_half l
  ** (if_then_else sp (lock_thn l q c) (lock_els l status_pool)))

let pool = (status_pool: ref bool
  & q: ref task_queue
  & c: ref int
  & ri: (r:ghost_mono_ref & inv (inv_ghost_queue r))
  & Lock.lock (lock_pool status_pool q c ri._1))

let mk_pool (status_pool: ref bool) (q: ref task_queue)
  (c: ref int) (ri: (r:ghost_mono_ref & inv (inv_ghost_queue r)))
  (lock: Lock.lock (lock_pool status_pool q c ri._1)): pool
= (| status_pool, q, c, ri, lock |)

let pool_alive (f: perm) (p: pool): vprop // f/2 permission to the ghost bool ref, true
= pts_to p._1 #(half_perm f) true


let locked_pool (p: pool): vprop =
  lock_pool p._1 p._2 p._3 p._4._1

```pulse
ghost fn elim_if_then
(b: bool) (thn: vprop) (els: vprop)
requires if_then_else b thn els ** pure b
ensures thn
{
  rewrite if_then_else b thn els as thn
}
```



//#push-options "--print_implicits"
```pulse
ghost fn
unfold_lock_pool_alive (#f: perm) (pl: pool)
requires pool_alive f pl ** locked_pool pl
//requires lock_pool pl._1 pl._2 pl._3 pl._4._1 ** pool_alive f pl
ensures pool_alive f pl ** (exists* sp l. pts_to pl._1 #one_half sp ** M.pts_to pl._4._1 one_half l **
  (exists* vq vc. pts_to pl._2 vq ** pts_to pl._3 vc ** pure (link l vq vc)))
{
  unfold locked_pool pl;
  unfold lock_pool;
  unfold pool_alive f pl;
  with sp gq. assert (pts_to pl._1 #one_half sp ** M.pts_to pl._4._1 one_half gq);
  pts_to_injective_eq pl._1;
  fold pool_alive f pl;
  elim_if_then _ _ _;
  unfold lock_thn; //_ pl._2 pl._3;
  ()
}
```

```pulse
ghost fn
fold_lock_pool_alive (#f: perm) (pl: pool)
requires pool_alive f pl ** (exists* sp l. pts_to pl._1 #one_half sp ** M.pts_to pl._4._1 one_half l **
  (exists* vq vc. pts_to pl._2 vq ** pts_to pl._3 vc ** pure (link l vq vc)))
ensures pool_alive f pl ** locked_pool pl
//requires lock_pool pl._1 pl._2 pl._3 pl._4._1 ** pool_alive f pl
{
  admit()
  (*
  unfold locked_pool pl;
  unfold lock_pool;
  unfold pool_alive f pl;
  with sp gq. assert (pts_to pl._1 #one_half sp ** M.pts_to pl._4._1 one_half gq);
  pts_to_injective_eq pl._1;
  fold pool_alive f pl;
  elim_if_then _ _ _;
  unfold lock_thn; //_ pl._2 pl._3;
  ()
  *)
}
```
(*
TODO: Actually launch workers...
*)
```pulse
fn setup_pool (n: int{n >= 1})
  requires emp
  returns pl: pool
  ensures pool_alive full_perm pl
{
  let ri: (r: ghost_mono_ref & inv (inv_ghost_queue r)) = create_ghost_queue ();

  let status_pool: ref bool = alloc true;
  share2 status_pool;

  let q: ref task_queue = alloc #task_queue [];
  let c: ref int = alloc 0;

  assert (pts_to q [] ** pts_to c 0 ** pure (link [] [] 0));
  assert (exists* vq vc. pts_to q vq ** pts_to c vc ** pure (link [] vq vc));
  fold lock_thn [] q c;
  fold (if_then_else true (lock_thn [] q c) (lock_els [] status_pool));

  fold (lock_pool status_pool q c ri._1);
  let lock = Lock.new_lock (lock_pool status_pool q c ri._1);

  let pl: pool = mk_pool status_pool q c ri lock;
  rewrite each status_pool as pl._1;
  fold pool_alive full_perm pl;
  pl
}
```

(*
probably this lock needs to be in the task queue?
*)

type handler (pl: pool) (post: vprop) =
  t:task & (pos:nat) & certificate pl._4._1 t pos //& Lock.lock (lock_task t)//(exists* v. pts_to t._4 #one_half v)

let mk_handler_pure (pl: pool) (post: vprop) (t: task) (pos: nat) (certif: certificate pl._4._1 t pos)
  //(lock: Lock.lock (lock_task t))
  : handler pl post
= (| t, pos, certif |)

```pulse
fn mk_handler
(pl: pool) (post: vprop) (t: task) 
(res: (pos:nat & certificate pl._4._1 t pos))
//(pos: nat) (certif: certificate pl._4._1 t pos)
requires GR.pts_to t._5 #one_half false
returns h: handler pl post
ensures GR.pts_to h._1._5 #one_half false
{
  //fold lock_task t;
  //let lock = Lock.new_lock (lock_task t);
  let h: handler pl post = mk_handler_pure pl post t res._1 res._2;
  rewrite each t as h._1;
  h
}
```
  
  //(lock: Lock.lock (exists* v. pts_to t._4 #one_half v)): handler pl post

(*
      GR.pts_to (Mkdtuple5?._5 t) (reveal (hide false)) ** 
      pts_to (Mkdtuple5?._4 t) (reveal (hide false)) ** 
    *)

(*
TODO:
ASSUMING!
*)
(*
val read_ghost_mono_ref (#a:Type) (#p:Preorder.preorder a) (#f: perm)
    (r:M.ref a p)
  : stt_atomic a #Unobservable emp_inames
  (exists* v. M.pts_to r f v) (fun vv -> M.pts_to r f vv)
  (* How wrong is this? *)
  *)
val read_ghost_mono_ref (#a:Type) (#p: Preorder.preorder a) (r:M.ref a p) (#n:erased a) (#p:perm)
  : stt a
        (M.pts_to r p n)
        (fun x -> M.pts_to r p n ** pure (reveal n == x))

let enqueue_add_task_get_actual (l: mono_list) (t: task) (vq: task_queue) (vc: int):
  Lemma (requires link l vq vc)
  (ensures link (enqueue_todo l t)._1 (t::vq) vc)
= ()

```pulse
ghost fn pulse_enqueue_add_task_get_actual (l: mono_list) (t: task) (vq: task_queue) (vc: int)
requires pure (link l vq vc)
ensures pure (link (enqueue_todo l t)._1 (t::vq) vc)
{
  ()
}
```



val assume_prop (p: prop):
stt unit emp (fun () -> pure p)

#push-options "--print_implicits"
```pulse
fn async #pre #post #f (pl: pool) (ta: (unit -> stt unit pre (fun () -> post)))
  requires pool_alive f pl ** pre
  returns h: handler pl post
  // returns pr: promise pl unit post, or handler
  ensures pool_alive f pl ** GR.pts_to h._1._5 #one_half false
  // ** pledge (task_done pr) post
{
  let ti: (t: task & inv (guarded_inv t._2 post)) = create_task ta;
  let t = ti._1;
  let itask: inv (guarded_inv t._2 post) = ti._2;

  let status_pool: ref bool = pl._1;
  let q: ref task_queue = pl._2;
  let c: ref int = pl._3;
  let r: ghost_mono_ref = pl._4._1;
  let i: inv (inv_ghost_queue r) = pl._4._2;
  let lock = pl._5;

  Lock.acquire pl._5;
  //show_proof_state;
  rewrite (lock_pool (Mkdtuple5?._1 pl) (Mkdtuple5?._2 pl) (Mkdtuple5?._3 pl) (Mkdtuple2?._1 (Mkdtuple5?._4 pl)))
    as locked_pool pl;//(lock_pool status_pool q c r);
  unfold_lock_pool_alive pl;

  rewrite each pl._1 as status_pool;
  rewrite each pl._2 as q;
  rewrite each pl._3 as c;
  rewrite each pl._4._1 as r;
  rewrite each pl._4._2 as i;
  rewrite each pl._5 as lock;
  rewrite each ti._1 as t;

  //with ll. assert (M.pts_to r one_half ll);
  let l: mono_list = read_ghost_mono_ref r;
  let ll: mono_list = (enqueue_todo l t)._1;
  with vq vc. assert (pts_to q vq ** pts_to c vc);
  let vq_: task_queue = !q;
  let vq': task_queue = Prims.Cons #task t vq_;
  assert pure (link l vq vc);
  assert pure (link ll vq' vc);

  rewrite each ti._1 as t;
  //share2 t._4._1;
  assert GR.pts_to t._5 #full_perm false;
  GR.share2 t._5;
  assert GR.pts_to t._5 #one_half false ** GR.pts_to t._5 #one_half false;
  let res: (pos:nat & certificate r t pos) = add_todo_task_to_queue r i t l;
  //assert M.pts_to r one_half (enqueue_todo l t)._1;

  assert pts_to q (reveal vq);
  q := vq'; //(enqueue_todo l t)._1;
  assert pure (link ll vq' vc);
  assert pool_alive f pl;
  with sp. assert pts_to status_pool #one_half sp ** M.pts_to r one_half ll;

  assert pool_alive f pl;
  rewrite each status_pool as pl._1;
  rewrite each q as pl._2;
  rewrite each c as pl._3;
  rewrite each r as pl._4._1;
  assert (exists* sp l. pts_to pl._1 #one_half sp ** M.pts_to pl._4._1 one_half l **
  (exists* vq vc. pts_to pl._2 vq ** pts_to pl._3 vc ** pure (link l vq vc)));
  fold_lock_pool_alive pl;
  rewrite (locked_pool pl) as lock_pool pl._1 pl._2 pl._3 pl._4._1;
  Lock.release pl._5;
  let h: handler pl post = mk_handler pl post t res;
  h
}
```

```pulse
ghost fn get_task_done (t: task) (f: perm)
requires pts_to t._4._1 #f true
ensures task_done t
{
  fold task_done t
}
```

```pulse
ghost fn close_lock_task (bdone: ref bool) (f: perm) (v: bool)
requires pts_to bdone #f v ** pure (if not v then f == one_half else true)
ensures lock_task bdone
{
  fold lock_task bdone;
}
```

(*
pool_alive is currently not necessary, because we never deallocate the reference where we say whether we're done...
*)
#pop-options
```pulse
fn await (#pl: pool) (#post: vprop) (h: handler pl post)
  requires pool_alive f pl
  ensures pool_alive f pl ** task_done h._1
{
  let mut task_is_done = false;
  rewrite emp as (if false then task_done h._1 else emp);
  let bdone: ref bool = h._1._4._1;
  let lock: Lock.lock (lock_task bdone) = h._1._4._2;
  while (let d = !task_is_done; not d)
    invariant b. (exists* d. pts_to task_is_done d ** pure (b == not d) ** (if d then task_done h._1 else emp)
    //** pure (bdone == h._1._4._1) 
    )
  {
    with d. assert pts_to task_is_done d;
    Lock.acquire lock;
    rewrite lock_task bdone
      as (exists* v f. pts_to bdone #f v ** pure (if not v then f == one_half else true));
    with v f. assert pts_to bdone #f v ** pure (if not v then f == one_half else true);
    let vdone: bool = !bdone;
    task_is_done := vdone;
    rewrite (match reveal d <: bool with | true -> task_done (Mkdtuple3?._1 h) | _ -> emp) as emp;
    if (vdone) {
      share bdone;
      assert pure (bdone == h._1._4._1);
      rewrite (pts_to bdone #(half_perm f) v) as pts_to h._1._4._1 #(half_perm f) true;
      assert pts_to h._1._4._1 #(half_perm f) true;
      get_task_done h._1 (half_perm f);
      rewrite task_done h._1 as (if true then task_done h._1 else emp);
      close_lock_task bdone (half_perm f) true;
      Lock.release h._1._4._2;
      assert pts_to task_is_done true;
      assert (pts_to task_is_done true ** (if true then task_done h._1 else emp));
      ()
    }
    else {
      rewrite emp as (if false then task_done h._1 else emp);
      close_lock_task bdone f false;
      Lock.release h._1._4._2;
      ()
    }
  };
  with d. assert pts_to task_is_done d;
  assert (if d then task_done h._1 else emp) ** pure (false = not d);
  elim_if_then d _ emp;
  //rewrite (if d then task_done h._1 else emp) as task_done h._1;
  ()
}
```



(*
+ there's an invariant somewhere that proves post of Some x
*)

(* where are stored the invariant? *)
(* in the certificate... *)


(*
let small_inv (r: erased (ghost_mono_ref task_elem)) (q: list task_elem) (c: int): vprop 
= exists_ (fun l -> pts_to_ghost_queue_half r l **
  tasks_res_own l one_half **
  pure (count_ongoing l = c /\ get_actual_queue l == q)
  ** (if c = 0 && L.length q = 0 then deadline r
  else pts_to_ghost_queue_half r l ** tasks_res_own l one_quart)
*)

(*
could be:


*)

```pulse
ghost fn intro_if_then
(b: bool) (thn: vprop) (els: vprop)
requires thn ** pure b
ensures if_then_else b thn els
{
  fold if_then_else b thn els;
}
```


```pulse
ghost fn open_lock_pool_alive
(p: pool) (f: perm)
requires pool_alive f p ** locked_pool p
ensures pool_alive f p ** (exists* gq q c.
  pts_to p._1 #one_half true ** pts_to_mono_queue p._4 full_perm gq ** HR.pts_to p._2 q ** pts_to p._3 c ** pure (link gq q c))
{
  unfold locked_pool p;
  unfold lock_pool;
  unfold pool_alive f p;

  with sp gq. assert (pts_to p._1 #one_half sp ** pts_to_mono_queue p._4 one_half gq);
 //** (if sp then (pts_to_mono_queue p._4 one_half gq ** (exists* q c. HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c))
  //  else (inv gq [] 0 ** (exists* f1 f2. pts_to p._1 #f1 sp ** pts_to_mono_queue p._4 f2 gq))));
  
  pts_to_injective_eq p._1;

  assert pure (sp);

  elim_if_then sp _ _;
(*
  rewrite (if sp then (lock_thn gq p._4 p._2 p._3) else (lock_els gq p._1 p._4))
    as (if true then (lock_thn gq p._4 p._2 p._3) else (lock_els gq p._1 p._4));


  rewrite (if true then (lock_thn gq p._4 p._2 p._3) else (lock_els gq p._1 p._4))
    as (lock_thn gq p._4 p._2 p._3);
    *)

  unfold lock_thn;


  with q c. assert (HR.pts_to p._2 q ** pts_to p._3 c ** pure (link gq q c));
  gather2_mono_queue p._4;

  fold pool_alive f p;
  ()
}
```

#push-options "--print_implicits"

```pulse
ghost fn close_lock_pool_alive
(p: pool) (f: perm)
requires (exists* gq q c.
  pts_to p._1 #one_half true ** pts_to_mono_queue p._4 full_perm gq ** HR.pts_to p._2 q ** pts_to p._3 c ** pure (link gq q c))
ensures locked_pool p
{
  let status_pool = p._1;
  with gq. assert (pts_to p._1 #one_half true ** pts_to_mono_queue p._4 full_perm gq);
  rewrite each p._1 as status_pool;
  // ** HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c);
  share2_mono_queue p._4;

  assert (pts_to status_pool #one_half true ** pts_to_mono_queue p._4 one_half gq);
  //assert (pts_to_mono_queue p._4 one_half gq ** HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c);

  //rewrite (pts_to_mono_queue p._4 one_half gq ** HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c)
  //as (pts_to_mono_queue p._4 one_half gq ** (exists* q c. HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c));

  //fold (if_then_else true (pts_to_mono_queue p._4 one_half gq ** (exists* q c. HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c))
   //   (inv gq [] 0ghost_queue ** (exists* f1 f2. pts_to p._1 #f1 true ** pts_to_mono_queue p._4 f2 gq)));
   fold lock_thn;

intro_if_then true (lock_thn gq p._4 p._2 p._3) (lock_els gq status_pool p._4);

assert (exists* gq. pts_to status_pool #one_half true ** pts_to_mono_queue p._4 one_half gq
  ** (if_then_else true (lock_thn gq p._4 p._2 p._3) (lock_els gq status_pool p._4)));

assert (pts_to status_pool #one_half true);
//with sp. assert pts_to p._1 #one_half sp;
//rewrite (pts_to p._1 #one_half true) as (exists* sp. pts_to p._1 #one_half sp);
//assert (exists* sp. pts_to p._1 #one_half sp);
assert (exists* sp gq. pts_to status_pool #one_half sp ** pts_to_mono_queue p._4 one_half gq);

 fold lock_pool status_pool p._2 p._3 p._4;
  (*
pts_to status_pool #one_half sp

  *)
  
  //fold lock_pool p._1 p._2 p._3 p._4;

(*
    assert (exists* sp gq. pts_to p._1 #one_half sp ** pts_to_mono_queue p._4 one_half gq
  ** if_then_else sp (pts_to_mono_queue p._4 one_half gq **
      (exists* q c. HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c))
    (inv gq [] 0 ** (exists* f1 f2. pts_to p._1 #f1 sp ** pts_to_mono_queue p._4 f2 gq)));


  assert (exists* sp. pts_to p._1 (reveal sp));

  show_proof_state;
  fold lock_pool p._1 p._2 p._3 p._4;
  *)

  
//  with sp. assert (pts_to p._1 (reveal sp));

(*
  rewrite (pts_to p._1 sp) as (pts_to p._1 (reveal sp));

  fold locked_pool p;
  *)


  //as (if_then_else sp (pts_to_mono_queue p._4 one_half gq ** (exists* q c. HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c))
   //   (inv gq [] 0 ** (exists* f1 f2. pts_to p._1 #f1 sp ** pts_to_mono_queue p._4 f2 gq)));

  //rewrite (pts_to_mono_queue p._4 one_half gq ** HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c)
  //fold locked_pool p;

  //rewrite (pts_to p._1 #one_half true ** pts_to_mono_queue p._4 one_half gq **
  //(pts_to_mono_queue p._4 one_half gq ** HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c))
  //as lock_pool p;


  admit()
}
```





let x = ()

let deadline (p: pool): vprop
= exists* f gq. pts_to_mono_queue p._4 f gq ** inv gq [] 0



val certificate (p:pool) (t: task_elem) (pos: nat): Type0
let secret_certificate (p: pool) (t: task_elem): Type0 = (pos: nat & certificate p t pos)

//val deadline (p: pool): vprop // ghost bool ref, false

val duplicate_deadline (p: pool):
stt_ghost unit (deadline p) (fun () -> deadline p ** deadline p)





//val small_inv (p: pool) (q: list task_elem) (c: int): vprop 


// 0. init queue with task
//val init_ghost_queue: stt_ghost pool emp (fun p -> inv p [] 0)





// 1. enqueue task
val spawn_task_ghost
(p: pool)
(q: list task_elem) (c: int)
(t: task_elem)
(#f: perm)
: stt_ghost (secret_certificate p t)
(small_inv p q c ** pts_to t._2 #three_quart None ** pool_alive f p)
(fun _ -> small_inv p (t::q) c ** pool_alive f p)

// 2. pop task todo
val pop_task_ghost
(p: pool)
(t: task_elem)
(q: list task_elem) (c: int)
: stt_ghost (secret_certificate p t) 
(small_inv p (t::q) c)
(fun _ -> small_inv p q (c + 1) ** pts_to t._2 #three_quart None)

(*
val prove_task_ongoing
  (#t: task_elem)
  (#pos: nat)
  (#v: option t._1)
  (r:gmref)
  (q: list task_elem) (c: int)
  (w:certificate r t pos)
: stt_ghost unit emp_inames
(small_inv r q c ** pts_to t._2 #three_quart v)
(fun () -> small_inv r q c ** pts_to t._2 #three_quart v ** pure (c > 0))

val prove_ongoing_non_neg
  (r: gmref)
  (q: list task_elem) (c: int)
: stt_ghost unit emp_inames
(small_inv r q c)
(fun () -> small_inv r q c ** pure (c >= 0))
*)

// 3. conclude a task
val conclude_task_ghost
(#t: task_elem)
(#pos: nat)
(p: pool)
(q: list task_elem) (c: int)
(x: t._1)
(w: secret_certificate p t):
stt_ghost unit 
(small_inv p q c ** pts_to t._2 #three_quart (Some x))
(fun () -> small_inv p q (c - 1)) //imp_vprop (c = 1 && L.length q = 0) (deadline r))

val proof_promise (#t: task_elem) (#pos: nat)
  (p: pool)
  (w:secret_certificate p t)
: stt_ghost unit 
(deadline p)
(fun () -> deadline p ** (exists* f v.
                          pts_to t._2 #f v ** pure (Some? v)))
