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

friend Pulse.Steel.Wrapper

noeq
type context_t = 
  | Engine_context  : uds:A.array U8.t -> 
                      context_t
  | L0_context      : cdi:A.larray U8.t 32 -> 
                      context_t
  | L1_context      : aliasKey_priv:A.larray U8.t 32 ->
                      cert_aliasKey:A.array U8.t ->
                      csr_deviceID:A.array U8.t ->
                      context_t

(* ----------- GLOBAL STATE ----------- *)

assume val dpe_hashf : nat -> nat
assume val sht_len : pos
assume val cht_len : pos
let cht_sig = mk_ht_sig cht_len nat context_t dpe_hashf 
let sht_sig = mk_ht_sig sht_len nat (ht_ref_t cht_sig) dpe_hashf 

// A table whose permission is stored in the lock 

```pulse
fn alloc_ht (l:pos)
  requires emp
  returns _:ht_ref_t
  ensures emp
{
  let ht = new_table l;
  let ht_ref = W.alloc #ht_t ht;
  let lk = W.new_lock (exists_ (fun _ht -> R.pts_to ht_ref full_perm _ht));
  ((| ht_ref, lk |) <: ht_ref_t)
}
```
let sht_ref : ht_ref_t = alloc_ht sht_len ()

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
  let cht_ref = alloc_ht cht_len;

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

assume val init_engine_ctxt (seed:A.array U8.t) : context_t
assume val prng (_:unit) : nat

(*
  InitializeContext: Part of DPE API 
  Create a context in the initial state (engine context) and store the context
  in the current session's context table. 
*)
```pulse
fn initialize_context (sid:nat) (seed:A.array U8.t)
  requires emp
  returns _:nat
  ensures emp
{
  let ctxt = init_engine_ctxt seed;
  let ctxt_hndl = prng ();

  let l_sht = dsnd sht_ref;
  W.acquire #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
  let sht = !(dfst sht_ref);

  let cht_ref = get sht sid;

  let l_cht = dsnd cht_ref;
  W.acquire #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
  let cht = !(dfst cht_ref);

  store cht ctxt_hndl ctxt;

  W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
  W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
  
  ctxt_hndl
}
```

(*


// DeriveChild: Part of DPE API 
// Execute the DICE layer associated with the current context and produce a 
// new context. Destroy the current context in the current session's context table 
// and store the new context in the table. 
fn DeriveChild (ctxt_hndl:A.array U32.t) (data:A.array U32.t) : A.array U32.t
{
  let cur_session = !session_id_ctr;
  let session_tbl = acquire session_tbl_lock;
  let ctxt_tbl_lock = get session_tbl cur_session;
  let ctxt_tbl = acquire ctxt_tbl_lock;

  let ctxt = get ctxt_tbl ctxt_hndl;
  let new_hndl = (PRNG);
  let new_ctxt: context_t = match ctxt
  | Engine_context -> (
      let engine_record = init_engine ctxt.uds data;
      let cdi = engine_main engine_record;
      L0_context cdi
    )
  | L0_context -> (
      let l0_record = init_l0 ctxt.cdi data;
      let (aliasKey_priv, cert_aliasKey, csr_deviceID) = l0_main l0_record;
      L1_context aliasKey_priv cert_aliasKey csr_deviceID
    )
  | _ -> Error;

  destroy ctxt_tbl ctxt_hndl;
  store ctxt_tbl new_hndl new_ctxt;
  new_hndl
}


// init_engine: Internal to DPE
// Build the record of DICE Engine state given the uds and l0 image
fn init_engine (uds:A.array U8.t) (l0_image:A.array U32.t) : engine_record_t
{
  ...
}


// init_l0: Internal to DPE
// Build the record of DICE L0 state given the cdi and fwid
fn init_l0 (cdi:A.larray U8.t 32) (fwid:A.array U32.t) : l0_record_t
{
  ...
}

*)