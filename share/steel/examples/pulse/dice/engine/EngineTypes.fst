module EngineTypes
open Pulse.Main
open Pulse.Steel.Wrapper
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
module R = Steel.ST.Reference
module A = Steel.ST.Array
module T = FStar.Tactics
module US = FStar.SizeT
module U8 = FStar.UInt8
open HACL
open Array

assume
val uds_is_enabled : vprop

assume
val uds_len : hashable_len 

assume
val uds_bytes : v:(Ghost.erased (Seq.seq U8.t)){ Seq.length v = US.v uds_len }

type dice_return_code = | DICE_SUCCESS | DICE_ERROR

let cdi_t = A.larray U8.t (US.v (digest_len dice_hash_alg))

(* Engine Context *)
noeq
type engine_context = { uds: A.larray U8.t (US.v uds_len); }

let engine_context_perm (c:engine_context) : vprop
  = A.pts_to c.uds full_perm uds_bytes `star` 
    uds_is_enabled `star`
    pure (A.is_full_array c.uds)

let mk_engine_context uds : engine_context = {uds}

(* Engine Record *)
noeq
type engine_record_t = {
  l0_image_header_size : signable_len;
  l0_image_header      : A.larray U8.t (US.v l0_image_header_size);
  l0_image_header_sig  : A.larray U8.t 64; (* secret bytes *)
  l0_binary_size       : hashable_len;
  l0_binary            : A.larray U8.t (US.v l0_binary_size);
  l0_binary_hash       : A.larray U8.t (US.v dice_digest_len); (*secret bytes *)
  l0_image_auth_pubkey : A.larray U8.t 32; (* secret bytes *)
}

type engine_record_repr = {
    l0_image_header      : Seq.seq U8.t;
    l0_image_header_sig  : Seq.seq U8.t;
    l0_binary            : Seq.seq U8.t;
    l0_binary_hash       : (s:Seq.seq U8.t{ Seq.length s = US.v dice_digest_len });
    l0_image_auth_pubkey : Seq.seq U8.t;
}

let mk_engine_repr  l0_image_header_size l0_image_header l0_image_header_sig
                    l0_binary_size l0_binary l0_binary_hash l0_image_auth_pubkey
  = {l0_image_header_size; l0_image_header; l0_image_header_sig;
     l0_binary_size; l0_binary; l0_binary_hash; l0_image_auth_pubkey}

let engine_record_perm (record:engine_record_t) (repr:engine_record_repr) 
  : vprop = 
  A.pts_to record.l0_image_header full_perm repr.l0_image_header `star`
  A.pts_to record.l0_image_header_sig full_perm repr.l0_image_header_sig `star`
  A.pts_to record.l0_binary full_perm repr.l0_binary `star`
  A.pts_to record.l0_binary_hash full_perm repr.l0_binary_hash `star`
  A.pts_to record.l0_image_auth_pubkey full_perm repr.l0_image_auth_pubkey
