module DPE
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
open X509
open EngineTypes
open L0Types
open EngineCore
open L0Core

friend Pulse.Steel.Wrapper
#set-options "--print_implicits --print_universes"

(* L1 Context -- to be moved *)

noeq
type l1_context = { aliasKey_priv: A.larray U8.t 32;
                    aliasKeyCRT: A.array U8.t;
                    deviceIDCSR: A.array U8.t; }

let l1_context_perm (c:l1_context)
  : vprop
  = exists_ (fun s -> A.pts_to c.aliasKey_priv full_perm s) `star`
    exists_ (fun s -> A.pts_to c.aliasKeyCRT full_perm s) `star`
    exists_ (fun s -> A.pts_to c.deviceIDCSR full_perm s)

let mk_l1_context aliasKey_priv aliasKeyCRT deviceIDCSR = { aliasKey_priv; aliasKeyCRT; deviceIDCSR }

(* Context *)
noeq
type context_t = 
  | Engine_context : c:engine_context -> context_t
  | L0_context     : c:l0_context -> context_t
  | L1_context     : c:l1_context -> context_t

let context_perm (t:context_t) : vprop = 
  match t with
  | Engine_context c -> engine_context_perm c
  | L0_context c -> l0_context_perm c
  | L1_context c -> l1_context_perm c

let mk_engine_context_t engine_context = Engine_context engine_context
let mk_l0_context_t l0_context = L0_context l0_context
let mk_l1_context_t l1_context = L1_context l1_context

let locked_context_t = c:context_t & L.lock (context_perm c)


(* Record *)
noeq
type record_t =
  | Engine_record : r:engine_record_t -> record_t
  | L0_record     : r:l0_record_t -> record_t

noeq
type repr_t = 
  | Engine_repr : r:engine_record_repr -> repr_t
  | L0_repr     : r:l0_record_repr -> repr_t

let record_perm (t_rec:record_t) (t_rep:repr_t) : vprop = 
  match t_rec with
  | Engine_record r -> (
    match t_rep with 
    | Engine_repr r0 -> engine_record_perm r r0
    | _ -> pure(false)
  )
  | L0_record r -> (
    match t_rep with
    | L0_repr r0 -> l0_record_perm r r0
    | _ -> pure(false)
  )

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

// TODO: 
assume val prng (_:unit) : nat

```pulse
fn init_engine_ctxt (uds:A.larray U8.t (US.v uds_len))
  requires (
    A.pts_to uds full_perm uds_bytes **
    uds_is_enabled **
    pure (A.is_full_array uds)
  )
  returns _:locked_context_t
  ensures emp
{
  let engine_context = mk_engine_context uds;

  rewrite (A.pts_to uds full_perm uds_bytes) 
    as (A.pts_to engine_context.uds full_perm uds_bytes);
  rewrite (A.pts_to engine_context.uds full_perm uds_bytes `star` 
           uds_is_enabled `star`
           pure (A.is_full_array engine_context.uds)) 
    as (engine_context_perm engine_context);

  let ctxt = mk_engine_context_t engine_context;

  rewrite (engine_context_perm engine_context) as (context_perm ctxt);

  let ctxt_lk = W.new_lock (context_perm ctxt);
  ((| ctxt, ctxt_lk |) <: locked_context_t)
}
```

```pulse
fn init_l0_ctxt (cdi:A.larray U8.t (US.v dice_digest_len))
  requires exists s. A.pts_to cdi full_perm s
  returns _:locked_context_t
  ensures emp
{
  let l0_context = mk_l0_context cdi;
// FIXME: pulse can't prove equality in the following two rewrites 
// has something to do with not unwrapping the existential
  // rewrite (exists_ (fun s -> A.pts_to cdi full_perm s)) 
  //   as (exists_ (fun s -> A.pts_to l0_context.cdi full_perm s)); 
  // rewrite (exists_ (fun s -> A.pts_to l0_context.cdi full_perm s)) as (l0_context_perm l0_context);
  drop_ (exists_ (fun s -> A.pts_to cdi full_perm s));
  assume_ (l0_context_perm l0_context);
  let ctxt = mk_l0_context_t l0_context;
  rewrite (l0_context_perm l0_context) as (context_perm ctxt);
  let ctxt_lk = W.new_lock (context_perm ctxt);
  ((| ctxt, ctxt_lk |) <: locked_context_t)
}
```

```pulse
fn init_l1_ctxt (aliasKey_priv: A.larray U8.t 32) (aliasKeyCRT: A.array U8.t) (deviceIDCSR: A.array U8.t)
  requires exists s. A.pts_to aliasKey_priv full_perm s ** 
    exists s. A.pts_to aliasKeyCRT full_perm s **
    exists s. A.pts_to deviceIDCSR full_perm s
  returns _:locked_context_t
  ensures emp
{
  let l1_context = mk_l1_context aliasKey_priv aliasKeyCRT deviceIDCSR;
// FIXME: pulse can't prove equality in the following two rewrites 
// has something to do with not unwrapping the existential
  // rewrite (exists_ (fun s -> A.pts_to aliasKey_priv full_perm s) `star`
  //          exists_ (fun s -> A.pts_to aliasKeyCRT full_perm s) `star`
  //          exists_ (fun s -> A.pts_to deviceIDCSR full_perm s)) 
  //   as (exists_ (fun s -> A.pts_to l1_context.aliasKey_priv full_perm s) `star`
  //       exists_ (fun s -> A.pts_to l1_context.aliasKeyCRT full_perm s) `star`
  //       exists_ (fun s -> A.pts_to l1_context.deviceIDCSR full_perm s)); 
  // rewrite (exists_ (fun s -> A.pts_to l1_context.aliasKey_priv full_perm s) `star`
  //          exists_ (fun s -> A.pts_to l1_context.aliasKeyCRT full_perm s) `star`
  //          exists_ (fun s -> A.pts_to l1_context.deviceIDCSR full_perm s)) as (l1_context_perm l1_context);
  drop_ (exists_ (fun s -> A.pts_to aliasKey_priv full_perm s) `star`
         exists_ (fun s -> A.pts_to aliasKeyCRT full_perm s) `star`
         exists_ (fun s -> A.pts_to deviceIDCSR full_perm s));
  assume_ (l1_context_perm l1_context);
  let ctxt = mk_l1_context_t l1_context;
  rewrite (l1_context_perm l1_context) as (context_perm ctxt);
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
    uds_is_enabled **
    pure (A.is_full_array uds)
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
    // FIXME: Pulse match doesn't handle
    // rewrite (context_perm cur_ctxt) as (engine_context_perm ctxt);
    drop_ (context_perm cur_ctxt);
    assume_ (engine_context_perm ctxt);
    rewrite (engine_context_perm ctxt) 
      as (A.pts_to ctxt.uds full_perm uds_bytes `star` 
          uds_is_enabled `star`
          pure (A.is_full_array ctxt.uds));

    // NOTE: we won't eventually release engine_context_perm because we won't 
    // own it anymore -- we will disable the uds and free the uds array

    match record {
    Engine_record r -> {
      match repr {
      Engine_repr r0 -> {       
        // FIXME: Pulse match doesn't handle
        // rewrite (record_perm record repr) as (engine_record_perm r r0); 
        drop_ (record_perm record repr);
        assume_ (engine_record_perm r r0);

        let cdi = new_array 0uy dice_digest_len;
        EngineCore.engine_main cdi ctxt.uds r; // FIXME: match on dice return type
        free_array ctxt.uds;

        let new_locked_context = init_l0_ctxt cdi;
        
        delete cht ctxt_hndl;
        store cht new_ctxt_hndl new_locked_context;

        // FIXME: Pulse match doesn't handle
        // rewrite (engine_record_perm r r0) as (record_perm record repr);
        drop_ (engine_record_perm r r0);
        assume_ (record_perm record repr);

        W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
        W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;

        new_ctxt_hndl
      }
      _ -> {
        // ERROR - bad invocation of DeriveChild
        zeroize_array uds_len ctxt.uds;
        disable_uds ();
        free_array ctxt.uds;

        W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
        W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
        0
      }}
    }
    _ -> {
      // ERROR - bad invocation of DeriveChild
      zeroize_array uds_len ctxt.uds;
      disable_uds ();
      free_array ctxt.uds;

      W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
      W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
      0
    }}
  }
  L0_context ctxt -> {
    // FIXME: Pulse match doesn't handle
    // rewrite (context_perm cur_ctxt) as (engine_context_perm ctxt);
    drop_ (context_perm cur_ctxt);
    assume_ (l0_context_perm ctxt);
    rewrite (l0_context_perm ctxt) 
      as (exists_ (fun (s:elseq U8.t (US.v dice_digest_len)) -> A.pts_to ctxt.cdi full_perm s) `star`
          pure (A.is_full_array ctxt.cdi));

    // NOTE: we won't eventually release l0_context_perm because we won't 
    // own it anymore -- we will free the cdi array

    match record {
    L0_record r -> {
      match repr {
      L0_repr r0 -> {
        let idcsr_ing = r.deviceIDCSR_ingredients;
        let akcrt_ing = r.aliasKeyCRT_ingredients;

        let deviceIDCRI_len = len_of_deviceIDCRI  idcsr_ing.version idcsr_ing.s_common 
                                                  idcsr_ing.s_org idcsr_ing.s_country;
        let aliasKeyTBS_len = len_of_aliasKeyTBS  akcrt_ing.serialNumber akcrt_ing.i_common 
                                                  akcrt_ing.i_org akcrt_ing.i_country 
                                                  akcrt_ing.s_common akcrt_ing.s_org 
                                                  akcrt_ing.s_country akcrt_ing.l0_version;
        let deviceIDCSR_len = length_of_deviceIDCSR deviceIDCRI_len;
        let aliasKeyCRT_len = length_of_aliasKeyCRT aliasKeyTBS_len;

        let aliasKey_pub = new_array 0uy 32sz;
        let aliasKey_priv = new_array 0uy 32sz;
        let deviceIDCSR = new_array 0uy (u32_to_us deviceIDCSR_len);
        let aliasKeyCRT = new_array 0uy (u32_to_us aliasKeyCRT_len);

        // FIXME: Pulse match doesn't handle
        // rewrite (record_perm record repr) as (l0_record_perm r r0); 
        drop_ (record_perm record repr);
        assume_ (l0_record_perm r r0);

        assume_ (pure(valid_hkdf_ikm_len (digest_len dice_hash_alg)));
        
        L0Core.l0_main  ctxt.cdi aliasKey_pub aliasKey_priv 
                        aliasKeyTBS_len aliasKeyCRT_len aliasKeyCRT 
                        deviceIDCRI_len deviceIDCSR_len deviceIDCSR r;
        free_array ctxt.cdi;
        free_array aliasKey_pub;

        let new_locked_context = init_l1_ctxt aliasKey_priv deviceIDCSR aliasKeyCRT;
        
        delete cht ctxt_hndl;
        store cht new_ctxt_hndl new_locked_context;

        // FIXME: Pulse match doesn't handle
        // rewrite (l0_record_perm r r0) as (record_perm record repr);
        drop_ (l0_record_perm r r0);
        assume_ (record_perm record repr);

        W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
        W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;

        new_ctxt_hndl
      }
      _ -> {
        // ERROR - bad invocation of DeriveChild
        zeroize_array dice_digest_len ctxt.cdi;
        free_array ctxt.cdi;

        W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
        W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
        0
      }}
    }
    _ -> {
      // ERROR - bad invocation of DeriveChild
      zeroize_array dice_digest_len ctxt.cdi;
      free_array ctxt.cdi;

      W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
      W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
      0
    }}
  }
  _ -> { 
    // ERROR - bad invocation of DeriveChild
    W.release #(context_perm cur_ctxt) ctxt_lk;
    W.release #(exists_ (fun n -> R.pts_to (dfst cht_ref) full_perm n)) l_cht;
    W.release #(exists_ (fun n -> R.pts_to (dfst sht_ref) full_perm n)) l_sht;
    0
  }}
}
```
