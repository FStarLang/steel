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

assume 
val u32_to_us (v:U32.t) : US.t

// TODO: move elsewhere
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
