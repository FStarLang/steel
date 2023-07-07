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
#set-options "--print_implicits --print_universes"


(* ----------- TYPES ----------- *)

noeq
type context_t = 
  | Engine_context  : uds:A.array U8.t -> 
                      context_t
  | L0_context      : cdi:A.array U8.t -> 
                      context_t
  | L1_context      : aliasKey_priv:A.larray U8.t 32 ->
                      cert_aliasKey:A.array U8.t ->
                      csr_deviceID:A.array U8.t ->
                      context_t

assume val destroy_ctxt (_:context_t) : unit

// TODO: add remaining engine record fields
noeq
type engine_record_t = {
  uds: A.array U8.t;
  l0_image: A.array U8.t;
}
let mk_engine_record uds l0_image = {uds; l0_image}

// TODO: add remaining engine record fields
noeq
type l0_record_t = {
  cdi: A.array U8.t;
  fwid: A.array U8.t;
}
let mk_l0_record cdi fwid = {cdi; fwid}


(* ----------- GLOBAL STATE ----------- *)

assume val dpe_hashf : nat -> nat
assume val sht_len : pos
assume val cht_len : pos
let cht_sig : ht_sig = mk_ht_sig cht_len nat context_t dpe_hashf 
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

(* call into DICE implementation *)
assume val engine_main (_:engine_record_t) : c:context_t{L0_context? c}
(* 
  init_engine: Internal to DPE
  Build the record of DICE Engine state given the uds and l0 image
*)
```pulse
fn init_engine (ctxt:(c:context_t{Engine_context? c})) (data:A.array U8.t)
  requires emp
  returns _:engine_record_t
  ensures emp
{
  admit();
  // TODO: initialize remaining fields
  // mk_engine_record ctxt.uds data
}
```

(* call into DICE implementation *)
assume val l0_main (_:l0_record_t) : c:context_t{L1_context? c}
(*
  init_l0: Internal to DPE
  Build the record of DICE L0 state given the cdi and fwid
*)
```pulse
fn init_l0 (ctxt:(c:context_t{L0_context? c})) (data:A.array U8.t)
  requires emp
  returns _:l0_record_t
  ensures emp
{
  admit();
  // TODO: initialize remaining fields
  // mk_l0_record ctxt.cdi data
}
```

(*
  DeriveChild: Part of DPE API 
  Execute the DICE layer associated with the current context and produce a 
  new context. Destroy the current context in the current session's context table 
  and store the new context in the table.
  NOTE: Returns 0 if called when ctxt has type L1_context (bad invocation)
*)
```pulse
fn derive_child (sid:nat) (ctxt_hndl:nat) (data:A.array U8.t)
  requires emp
  returns _:nat
  ensures emp
{
  let new_ctxt_hndl = prng ();

  let l_sht = dsnd sht_ref;
  W.acquire #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
  let sht = !(dfst sht_ref);

  let cht_ref = get sht sid;

  let l_cht = dsnd cht_ref;
  W.acquire #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
  let cht = !(dfst cht_ref);

  let cur_ctxt = get cht ctxt_hndl;
  let a = Engine_context? cur_ctxt;
  let b = L0_context? cur_ctxt;
  if a {
    let engine_rec = init_engine cur_ctxt data;
    let new_ctxt = engine_main engine_rec;
    
    destroy_ctxt cur_ctxt;
    delete cht ctxt_hndl;
    store cht new_ctxt_hndl new_ctxt;

    W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
    W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;

    new_ctxt_hndl
  } else {
    if b {
      let l0_rec = init_l0 cur_ctxt data;
      let new_ctxt = l0_main l0_rec;
      
      destroy_ctxt cur_ctxt;
      delete cht ctxt_hndl;
      store cht new_ctxt_hndl new_ctxt;

      W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
      W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;

      new_ctxt_hndl
    } else {
      W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
      W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
      0
    };
  };
}
```
