module DPEPseudo
module A = Steel.ST.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open HACL
open L0Types

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

noeq
type engine_record_t = {
  uds: A.array U8.t;
  l0_image_header_size : signable_len;
  l0_image_header      : A.larray U8.t (US.v l0_image_header_size);
  l0_image_header_sig  : A.larray U8.t 64; (* secret bytes *)
  l0_binary_size       : hashable_len;
  l0_binary            : A.larray U8.t (US.v l0_binary_size);
  l0_binary_hash       : A.larray U8.t (US.v dice_digest_len); (*secret bytes *)
  l0_image_auth_pubkey : A.larray U8.t 32; (* secret bytes *)
}

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
type record_t =
  | Engine_record : r:engine_record_t -> record_t
  | L0_record     : r:l0_record_t -> record_t