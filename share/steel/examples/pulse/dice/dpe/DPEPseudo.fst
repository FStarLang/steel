module DPEPseudo
open Pulse.Main
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
open Pulse.Steel.Wrapper
module W = Pulse.Steel.Wrapper
module L = Steel.ST.SpinLock
module A = Steel.ST.Array
module R = Steel.ST.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open Array
open HashTable
open HACL
open CommonTypes
open EngineTypes
open EngineCore

friend Pulse.Steel.Wrapper
#set-options "--print_implicits --print_universes"

(* ----------- GLOBAL STATE ----------- *)

assume val dpe_hashf : nat -> nat
assume val sht_len : pos
assume val cht_len : pos
let cht_sig : ht_sig = mk_ht_sig cht_len nat locked_context_t dpe_hashf 
let sht_sig : ht_sig = mk_ht_sig sht_len nat (ht_ref_t cht_sig) dpe_hashf 

// A table whose permission is stored in the lock 

```pulse
fn alloc_ht (#s:ht_sig)
  requires emp
  returns _:ht_ref_t s
  ensures emp
{
  let ht = new_table #s;
  let ht_ref = W.alloc #(ht_t s) ht;
  let lk = W.new_lock (exists_ (fun _ht -> R.pts_to ht_ref full_perm _ht));
  ((| ht_ref, lk |) <: ht_ref_t s)
}
```
let sht_ref : ht_ref_t sht_sig = alloc_ht #sht_sig ()

// A number that tracks the next session ID

```pulse
fn alloc_sid (_:unit)
  requires emp
  returns _:sid_ref_t
  ensures emp
{
  let sid_ref = W.alloc #nat 0;
  let lk = W.new_lock (exists_ (fun n -> R.pts_to sid_ref full_perm n));
  ((| sid_ref, lk |) <: sid_ref_t)
}
```
let sid_ref : sid_ref_t = alloc_sid () ()


(* ----------- IMPLEMENTATION ----------- *)

(*
  OpenSession: Part of DPE API 
  Create a context table and context table lock for the new session. 
  Add the context table lock to the session table. 
  NOTE: Current implementation disregards session protocol 
*)
```pulse
fn open_session (_:unit)
  requires emp
  ensures emp
{
  let cht_ref = alloc_ht #cht_sig;

  let l_sid = dsnd sid_ref;
  let l_sht = dsnd sht_ref;

  W.acquire #(exists_ (fun n -> R.pts_to (dfst sid_ref) full_perm n)) l_sid;
  W.acquire #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
  
  let sid = !(dfst sid_ref);
  let sht = !(dfst sht_ref);

  store sht sid cht_ref;
  dfst sid_ref := sid + 1;

  W.release #(exists_ (fun n -> R.pts_to (dfst sid_ref) full_perm n)) l_sid;
  W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
  ()
}
```

(* 
  CloseSession: Part of DPE API 
  Destroy the context table for the session and remove the reference
  to it from the session table. 
  NOTE: Current implementation disregards session protocol 
*)
```pulse
fn close_session (sid:nat)
  requires emp
  ensures emp
{
  let l_sht = dsnd sht_ref;
  W.acquire #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
  let sht = !(dfst sht_ref);

  let cht_ref = get sht sid;

  let l_cht = dsnd cht_ref;
  W.acquire #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
  let cht = !(dfst cht_ref);

  destroy cht;
  W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;

  delete sht sid;
  W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
}
```

assume val prng (_:unit) : nat

```pulse
fn init_engine_ctxt (uds:A.larray U8.t (US.v uds_len))
  requires (
    A.pts_to uds full_perm uds_bytes **
    uds_is_enabled
  )
  returns _:locked_context_t
  ensures emp
{
  let engine_context = mk_engine_context uds;
  rewrite (A.pts_to uds full_perm uds_bytes) as (A.pts_to engine_context.uds full_perm uds_bytes);
  rewrite (A.pts_to engine_context.uds full_perm uds_bytes `star` uds_is_enabled) as (engine_context_perm engine_context);
  let ctxt = mk_engine_context_t engine_context;
  rewrite (engine_context_perm engine_context) as (context_perm ctxt);
  let ctxt_lk = W.new_lock (context_perm ctxt);
  ((| ctxt, ctxt_lk |) <: locked_context_t)
}
```

```pulse
fn init_l0_ctxt (cdi:A.larray U8.t 32)
  requires exists_ (fun s -> A.pts_to cdi full_perm s)
  returns _:locked_context_t
  ensures emp
{
  let l0_context = mk_l0_context cdi;
  rewrite (exists_ (fun s -> A.pts_to cdi full_perm s)) 
    as (exists_ (fun s -> A.pts_to l0_context._cdi full_perm s)); // FIXME: pulse can't figure this out but a similar rewrite works in line 138
                                                                  // so it must have to do with the existentially quantified var
  rewrite (exists_ (fun s -> A.pts_to l0_context._cdi full_perm s)) as (l0_context_perm l0_context);
  let ctxt = mk_l0_context_t l0_context;
  rewrite (l0_context_perm l0_context) as (context_perm ctxt);
  let ctxt_lk = W.new_lock (context_perm ctxt);
  ((| ctxt, ctxt_lk |) <: locked_context_t)
}
```

(*
  InitializeContext: Part of DPE API 
  Create a context in the initial state (engine context) and store the context
  in the current session's context table. 
*)
```pulse
fn initialize_context (sid:nat) (uds:A.larray U8.t (US.v uds_len))
  requires (
    A.pts_to uds full_perm uds_bytes ** 
    uds_is_enabled
  )
  returns _:nat
  ensures emp
{
  let locked_context = init_engine_ctxt uds;
  let ctxt_hndl = prng ();

  let l_sht = dsnd sht_ref;
  W.acquire #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
  let sht = !(dfst sht_ref);

  let cht_ref = get sht sid;

  let l_cht = dsnd cht_ref;
  W.acquire #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
  let cht = !(dfst cht_ref);

  store cht ctxt_hndl locked_context;

  W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
  W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
  
  ctxt_hndl
}
```

assume val zero_ctxt (c:context_t) 
  : (context_perm c)
    unit
    (context_perm c)
     
(*
  DeriveChild: Part of DPE API 
  Execute the DICE layer associated with the current context and produce a 
  new context. Destroy the current context in the current session's context table 
  and store the new context in the table.
  NOTE: Returns 0 if called when ctxt has type L1_context (bad invocation)
*)
```pulse
fn derive_child (sid:nat) (ctxt_hndl:nat) (record:record_t) (repr:repr_t)
  requires record_perm record repr
  returns _:nat
  ensures record_perm record repr
{
  let new_ctxt_hndl = prng ();

  let l_sht = dsnd sht_ref;
  W.acquire #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
  let sht = !(dfst sht_ref);

  let cht_ref = get sht sid;

  let l_cht = dsnd cht_ref;
  W.acquire #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
  let cht = !(dfst cht_ref);

  let locked_ctxt = get cht ctxt_hndl;

  let cur_ctxt = dfst locked_ctxt;
  let ctxt_lk = dsnd locked_ctxt;
  W.acquire #(context_perm cur_ctxt) ctxt_lk;

  match cur_ctxt {
  Engine_context ctxt -> {
    rewrite (context_perm cur_ctxt) as (engine_context_perm ctxt); // FIXME: Pulse can't seem to infer this even though we do the same matching as context_perm
    rewrite (engine_context_perm ctxt) 
      as (A.pts_to ctxt.uds full_perm uds_bytes `star` uds_is_enabled);
    
    match record {
    Engine_record r -> {
      match repr {
        Engine_repr r0 -> {          
          rewrite (record_perm record repr) as (engine_record_perm r r0); // FIXME: Pulse can't seem to infer this even though we do the same matching as record_perm

          let cdi = new_array 0uy dice_digest_len;
          EngineCore.engine_main cdi ctxt.uds r;

          let new_locked_context = init_l0_ctxt cdi;
          
          zero_ctxt cur_ctxt;
          delete cht ctxt_hndl;
          store cht new_ctxt_hndl new_locked_context;

          W.release #(context_perm cur_ctxt) ctxt_lk;
          W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
          W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;

          new_ctxt_hndl 
        }
        _ -> {admit()}
      }
    }
    _ -> {
      // ERROR
      W.release #(context_perm cur_ctxt) ctxt_lk;
      W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
      W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
      0
    }}
  }
  L0_context ctxt -> { 
    match record {
    L0_record record -> {
      admit()
      // let new_ctxt = l0_main record;
      
      // destroy_ctxt cur_ctxt;
      // delete cht ctxt_hndl;
      // store cht new_ctxt_hndl new_ctxt;

      // W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
      // W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;

      // new_ctxt_hndl
    }
    _ -> {
      // ERROR
      W.release #(context_perm cur_ctxt) ctxt_lk;
      W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
      W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
      0
    }}
  }
  _ -> { 
    // ERROR
    W.release #(context_perm cur_ctxt) ctxt_lk;
    W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
    W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
    0
  }}
}
```
