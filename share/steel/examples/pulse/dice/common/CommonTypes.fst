module CommonTypes
open Pulse.Main
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module L = Steel.ST.SpinLock
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open HACL
open EngineTypes
open L0Types

(* ----------- CONTEXT ----------- *)

noeq
type engine_context = { uds: A.array U8.t; }
let engine_context_perm (c:engine_context) : vprop
  = A.pts_to c.uds full_perm uds_bytes `star` uds_is_enabled
let mk_engine_context uds : engine_context = {uds}

noeq
type l0_context = { _cdi: A.array U8.t; }
let l0_context_perm (c:l0_context) : vprop
  = exists_ (fun s -> A.pts_to c._cdi full_perm s)
let mk_l0_context _cdi : l0_context = {_cdi}

noeq
type l1_context = { aliasKey_priv: A.larray U8.t 32;
                    cert_aliasKey: A.array U8.t;
                    csr_deviceID: A.array U8.t; }
let l1_context_perm (c:l1_context)
  : vprop
  = exists_ (fun s -> A.pts_to c.aliasKey_priv full_perm s) `star`
    exists_ (fun s -> A.pts_to c.cert_aliasKey full_perm s) `star`
    exists_ (fun s -> A.pts_to c.csr_deviceID full_perm s)
let mk_l1_context aliasKey_priv cert_aliasKey csr_deviceID = { aliasKey_priv; cert_aliasKey; csr_deviceID }

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

(* ----------- RECORD ----------- *)

noeq
type l0_record_t = {
  cdi: A.larray U8.t 32;
  fwid: A.larray U8.t 32;
  deviceID_label_len: hkdf_lbl_len; (* should be U32 *)
  deviceID_label: A.larray U8.t (US.v deviceID_label_len); (* public bytes *)
  aliasKey_label_len: hkdf_lbl_len; (* should be U32 *)
  aliasKey_label: A.larray U8.t (US.v aliasKey_label_len); (* public bytes *)
  deviceIDCSR_ingredients: deviceIDCSR_ingredients_t;
  aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t;
}

noeq
type l0_record_repr = {
  cdi: Seq.seq U8.t;
  fwid: Seq.seq U8.t;
  deviceID_label: Seq.seq U8.t;
  aliasKey_label: Seq.seq U8.t;
}

let mk_l0_repr cdi fwid deviceID_label aliasKey_label 
  = {cdi; fwid; deviceID_label; aliasKey_label}

let l0_record_perm (record:l0_record_t) (repr:l0_record_repr) : vprop = 
  A.pts_to record.cdi full_perm repr.cdi `star`
  A.pts_to record.fwid full_perm repr.fwid `star`
  A.pts_to record.deviceID_label full_perm repr.deviceID_label `star`
  A.pts_to record.aliasKey_label full_perm repr.aliasKey_label

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
