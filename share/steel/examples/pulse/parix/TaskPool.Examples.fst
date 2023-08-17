module TaskPool.Examples

open Pulse.Lib.Pervasives
open Promises
open TaskPool

assume
val qsv : nat -> vprop
assume
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
  drop_ (pool_done p);
  ()
}
```

```pulse
fn qs12 (_:unit)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2
  {
    qsc 1;
    qsc 2
  }
```

```pulse
fn qsh (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  spawn p qs12;
  // could do the same thing for 3&4... it's gonna work.
  // also qs12 could spawn and join its tasks, it would clearly work
  spawn p (fun () -> qsc 3);
  spawn p (fun () -> qsc 4);
  teardown_pool p;
  redeem_promise (pool_done p) (qsv 1 ** qsv 2);
  redeem_promise (pool_done p) (qsv 3);
  redeem_promise (pool_done p) (qsv 4);
  drop_ (pool_done p);
  ()
}
```

```pulse
fn qs12_par (p:pool)
  requires pool_alive p
  returns _:unit
  ensures pool_alive p ** promise (pool_done p) (qsv 1) ** promise (pool_done p) (qsv 2)
  {
    spawn p (fun () -> qsc 1);
    spawn p (fun () -> qsc 2);
    ()
  }
```

[@@expect_failure]
```pulse
fn qsh_par (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  spawn p (fun () -> qs12_par p);
  (* Ah! This cannot work right now since we need to share part
  of the pool_alive vprop to the spawned task, so we have
  to index pool_alive with a permission, and allow
  share/gather. *)
  
  spawn p (fun () -> qsc 3);
  spawn p (fun () -> qsc 4);
  teardown_pool p;
  redeem_promise (pool_done p) (qsv 1)
  redeem_promise (pool_done p) (qsv 2);
  redeem_promise (pool_done p) (qsv 3);
  redeem_promise (pool_done p) (qsv 4);
  drop_ (pool_done p);
  ()
}
```
