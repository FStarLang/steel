module HashTable
open Pulse.Main
open Pulse.Steel.Wrapper
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
module R = Steel.ST.Reference
module L = Steel.ST.SpinLock
module US = FStar.SizeT
module U32 = FStar.UInt32

// Hash table types 

assume val ht_t : Type0

type ht_ref_t = r:R.ref ht_t & L.lock (exists_ (fun ht -> R.pts_to r full_perm ht))

assume val new_table (_:unit) : ht_t

// Session ID types

type sid_ref_t = r:R.ref US.t & L.lock (exists_ (fun n -> R.pts_to r full_perm n))
