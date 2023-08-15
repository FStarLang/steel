module DPE
open Pulse.Lib.Pervasives
open HACL
open X509
open EngineTypes
open EngineCore
open L0Types
open L0Core
module L = Pulse.Lib.SpinLock
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open LinearScanHashTable
open PulseHashTable
module PHT = PulseHashTable
module LSHT = LinearScanHashTable

(* L1 Context -- no dedicated L1 logic, so there's no good place for this to live *)
noeq
type l1_context = { deviceID_priv: A.larray U8.t (US.v v32us);
                    deviceID_pub: A.larray U8.t (US.v v32us);
                    aliasKey_priv: A.larray U8.t (US.v v32us);
                    aliasKey_pub: A.larray U8.t (US.v v32us);
                    aliasKeyCRT: A.array U8.t;
                    deviceIDCSR: A.array U8.t; }

let l1_context_perm (c:l1_context)
  : vprop
  = exists_ (fun s -> A.pts_to c.deviceID_priv s) **
    exists_ (fun s -> A.pts_to c.deviceID_pub s) **
    exists_ (fun s -> A.pts_to c.aliasKey_priv s) **
    exists_ (fun s -> A.pts_to c.aliasKey_pub s) **
    exists_ (fun s -> A.pts_to c.aliasKeyCRT s) **
    exists_ (fun s -> A.pts_to c.deviceIDCSR s) **
    pure (
      A.is_full_array c.deviceID_priv /\
      A.is_full_array c.deviceID_pub /\
      A.is_full_array c.aliasKey_priv /\
      A.is_full_array c.aliasKey_pub /\
      A.is_full_array c.aliasKeyCRT /\
      A.is_full_array c.deviceIDCSR
    )

let mk_l1_context deviceID_priv deviceID_pub aliasKey_priv aliasKey_pub aliasKeyCRT deviceIDCSR 
  = { deviceID_priv; deviceID_pub; aliasKey_priv; aliasKey_pub; aliasKeyCRT; deviceIDCSR }

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

type sid_ref_t = r:R.ref nat & L.lock (exists_ (fun n -> R.pts_to r n))

val dpe_hashf : nat -> US.t
val sht_len : pos_us
val cht_len : pos_us
let cht_sig : pht_sig_us = mk_pht_sig_us nat locked_context_t dpe_hashf
let sht_sig : pht_sig_us = mk_pht_sig_us nat (locked_ht_t cht_sig) dpe_hashf 

val locked_sht : locked_ht_t sht_sig
val sid_ref : sid_ref_t

val prng (_:unit) : nat

val init_l0_ctxt (cdi:A.larray U8.t (US.v dice_digest_len)) (#s:erased (elseq U8.t dice_digest_len))
  : stt locked_context_t
    (A.pts_to cdi s ** pure (A.is_full_array cdi))
    (fun _ -> A.pts_to cdi s)

val init_l1_ctxt (deviceIDCSR_len: US.t) (aliasKeyCRT_len: US.t) 
                (deviceID_priv: A.larray U8.t (US.v v32us)) (deviceID_pub: A.larray U8.t (US.v v32us))
                (aliasKey_priv: A.larray U8.t (US.v v32us)) (aliasKey_pub: A.larray U8.t (US.v v32us)) 
                (deviceIDCSR: A.larray U8.t (US.v deviceIDCSR_len)) (aliasKeyCRT: A.larray U8.t (US.v aliasKeyCRT_len))
                (#s1 #s2 #s3 #s4: erased (elseq U8.t v32us)) 
                (#s5:erased (elseq U8.t deviceIDCSR_len))
                (#s6:erased (elseq U8.t aliasKeyCRT_len))
  : stt locked_context_t
     (A.pts_to deviceID_priv s1 ** 
      A.pts_to deviceID_pub s2 **  
      A.pts_to aliasKey_priv s3 **  
      A.pts_to aliasKey_pub s4 **  
      A.pts_to deviceIDCSR s5 ** 
      A.pts_to aliasKeyCRT s6) 
     (fun _ -> 
      A.pts_to deviceID_priv s1 **  
      A.pts_to deviceID_pub s2 ** 
      A.pts_to aliasKey_priv s3 **  
      A.pts_to aliasKey_pub s4 **  
      A.pts_to deviceIDCSR s5 ** 
      A.pts_to aliasKeyCRT s6)