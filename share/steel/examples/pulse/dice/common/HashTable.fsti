module HashTable
open Pulse.Main
open Pulse.Steel.Wrapper
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
module A = Steel.ST.Array
module US = FStar.SizeT
module U32 = FStar.UInt32

val session_table_len : US.t
val context_table_len : US.t

val new_table (_:unit) 
  : stt (A.array U32.t) 
     (requires emp)
     (ensures fun a ->
        A.pts_to a full_perm (Seq.create (US.v session_table_len) 0ul) `star`
        pure (A.length a == US.v session_table_len /\ A.is_full_array a))
