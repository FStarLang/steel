module CommonTypes
module A = Steel.ST.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open HACL
open EngineTypes
open L0Types

(* ----------- CONTEXT ----------- *)
noeq
type engine_context = { uds: A.array U8.t; }

noeq
type l0_context = { _cdi: A.array U8.t; }

noeq
type l1_context = { aliasKey_priv: A.larray U8.t 32;
                    cert_aliasKey: A.array U8.t;
                    csr_deviceID: A.array U8.t; }

// noeq
// type context_t = 
//   | Engine_context  : uds:A.array U8.t -> 
//                       context_t
//   | L0_context      : cdi:A.array U8.t -> 
//                       context_t
//   | L1_context      : aliasKey_priv:A.larray U8.t 32 ->
//                       cert_aliasKey:A.array U8.t ->
//                       csr_deviceID:A.array U8.t ->
//                       context_t

noeq
type context_t = 
  | Engine_context :engine_context -> context_t
  | L0_context     : c:l0_context -> context_t
  | L1_context     : c:l1_context -> context_t

let mk_engine_context uds = Engine_context { uds }
let mk_l0_context _cdi = L0_context { _cdi }
let mk_l1_context aliasKey_priv cert_aliasKey csr_deviceID = L1_context { aliasKey_priv; cert_aliasKey; csr_deviceID }



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
let mk_l0_record  cdi fwid deviceID_label_len deviceID_label 
                  aliasKey_label_len aliasKey_label 
                  deviceIDCSR_ingredients aliasKeyCRT_ingredients 
  = {cdi; fwid; deviceID_label_len; deviceID_label; 
     aliasKey_label_len; aliasKey_label; 
     deviceIDCSR_ingredients; aliasKeyCRT_ingredients}
     
noeq
type record_t =
  | Engine_record : r:engine_record_t -> record_t
  | L0_record     : r:l0_record_t -> record_t

noeq
type repr_t = 
  | Engine_repr : r:engine_record_repr -> repr_t
  // | L0_repr : r:l0_record_repr -> repr_t
