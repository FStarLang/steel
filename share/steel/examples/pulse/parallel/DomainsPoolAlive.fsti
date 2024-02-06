module DomainsPoolAlive

open Pulse.Lib.Pervasives
module Lock = Pulse.Lib.SpinLock
module HR = Pulse.Lib.HigherReference
module M = Pulse.Lib.GhostMonotonicHigherReference

let thunk a p
  = unit -> stt unit (pts_to p #one_half None) (fun () ->
    exists* v. pts_to p #one_half (Some v))

(*
+ there's an invariant somewhere that proves post of Some x
*)

(* where are stored the invariant? *)
(* in the certificate... *)

let task_elem = (
  a: Type0 // return type of the computation
  & p: ref (option a) // the reference where we put the result of the computation
  & thunk a p // the computation
)

let task_queue: Type u#1 = list task_elem
// depends negatively on pool

(* also ghost queue? *)
val mono_queue_ref: Type0
val mono_queue: Type0 (* not 0? *)

val pts_to_mono_queue
  (ghost_queue: mono_queue_ref) (f: perm) (value: mono_queue): vprop

val gather2_mono_queue (r:mono_queue_ref) (#x0 #x1:erased mono_queue)
  : stt_ghost unit
      (pts_to_mono_queue r one_half x0 ** pts_to_mono_queue r one_half x1)
      (fun _ -> pts_to_mono_queue r full_perm x0 ** pure (x0 == x1))

(* Share/gather specialized to half permission *)
val share2_mono_queue (r:mono_queue_ref) (#v:erased mono_queue)
  : stt_ghost unit
      (pts_to_mono_queue r full_perm v)
      (fun _ -> pts_to_mono_queue r one_half v ** pts_to_mono_queue r one_half v)



val inv (gq: mono_queue) (q: task_queue) (c: int): vprop

let if_then_else (b: bool) (thn: vprop) (els: vprop): vprop
= if b then thn else els

```pulse
ghost fn elim_if_then
(b: bool) (thn: vprop) (els: vprop)
requires if_then_else b thn els ** pure b
ensures thn
{
  rewrite if_then_else b thn els as thn
}
```

```pulse
ghost fn intro_if_then
(b: bool) (thn: vprop) (els: vprop)
requires thn ** pure b
ensures if_then_else b thn els
{
  fold if_then_else b thn els;
}
```

let lock_thn gq ghost_queue queue counter: vprop
= (pts_to_mono_queue ghost_queue one_half gq ** (exists* q c. HR.pts_to queue q ** pts_to counter c ** inv gq q c))

let lock_els gq status_pool ghost_queue: vprop
= (inv gq [] 0 ** (exists* f1 f2. pts_to status_pool #f1 false ** pts_to_mono_queue ghost_queue f2 gq))


let lock_pool
  (status_pool: ref bool)
  (queue: HR.ref task_queue)
  (counter: ref int)
  (ghost_queue: mono_queue_ref)
: vprop
= (exists* sp gq. pts_to status_pool #one_half sp ** pts_to_mono_queue ghost_queue one_half gq
  ** (if_then_else sp (lock_thn gq ghost_queue queue counter) (lock_els gq status_pool ghost_queue)))


let pool = (status_pool: ref bool
  & queue: HR.ref task_queue
  & counter: ref int
  & ghost_queue: mono_queue_ref
  & Lock.lock (lock_pool status_pool queue counter ghost_queue))

let locked_pool (p: pool): vprop =
  lock_pool p._1 p._2 p._3 p._4


let pool_alive (f: perm) (p: pool): vprop // f/2 permission to the ghost bool ref, true
= pts_to p._1 #(half_perm f) true

```pulse
ghost fn open_lock_pool_alive
(p: pool) (f: perm)
requires pool_alive f p ** locked_pool p
ensures pool_alive f p ** (exists* gq q c.
  pts_to p._1 #one_half true ** pts_to_mono_queue p._4 full_perm gq ** HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c)
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


  with q c. assert (HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c);
  gather2_mono_queue p._4;

  fold pool_alive f p;
  ()
}
```

```pulse
ghost fn close_lock_pool_alive
(p: pool) (f: perm)
requires (exists* gq q c.
  pts_to p._1 #one_half true ** pts_to_mono_queue p._4 full_perm gq ** HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c)
ensures locked_pool p
{
  with gq. assert (pts_to p._1 #one_half true ** pts_to_mono_queue p._4 full_perm gq);
  // ** HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c);
  share2_mono_queue p._4;

  assert (pts_to p._1 #one_half true ** pts_to_mono_queue p._4 one_half gq);
  //assert (pts_to_mono_queue p._4 one_half gq ** HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c);

  //rewrite (pts_to_mono_queue p._4 one_half gq ** HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c)
  //as (pts_to_mono_queue p._4 one_half gq ** (exists* q c. HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c));

  //fold (if_then_else true (pts_to_mono_queue p._4 one_half gq ** (exists* q c. HR.pts_to p._2 q ** pts_to p._3 c ** inv gq q c))
   //   (inv gq [] 0ghost_queue ** (exists* f1 f2. pts_to p._1 #f1 true ** pts_to_mono_queue p._4 f2 gq)));
   fold lock_thn;

intro_if_then true (lock_thn gq p._4 p._2 p._3) (lock_els gq p._1 p._4);

assert (exists* gq. pts_to p._1 #one_half true ** pts_to_mono_queue p._4 one_half gq
  ** (if_then_else true (lock_thn gq p._4 p._2 p._3) (lock_els gq p._1 p._4)));


  fold lock_pool p._1 p._2 p._3 p._4;
  
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
