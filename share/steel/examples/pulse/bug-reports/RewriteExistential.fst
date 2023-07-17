module RewriteExistential
open Pulse.Main
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
open Pulse.Steel.Wrapper
module W = Pulse.Steel.Wrapper
module A = Steel.ST.Array
module US = FStar.SizeT
module U8 = FStar.UInt8

assume val len : nat
noeq
type my_rec = { a:A.array U8.t }
let mk_rec a = { a }
let rec_perm (r:my_rec) : vprop 
  = exists_ (fun (s:(Seq.seq U8.t){Seq.length s == len}) -> A.pts_to r.a full_perm s) `star` pure(A.is_full_array r.a)

```pulse
fn rewrite_existential (a: A.array U8.t) (#s:(s:Ghost.erased (Seq.seq U8.t){Seq.length s == len}))
  requires A.pts_to a full_perm s ** pure(A.is_full_array a)
  ensures emp
{
  let r = mk_rec a;
  // rewrite (exists_ (fun s -> A.pts_to a full_perm s))
  //   as (exists_ (fun s -> A.pts_to r.a full_perm s));
  assume_ (exists_ (fun (s:(Seq.seq U8.t){Seq.length s == len}) -> A.pts_to r.a full_perm s));
  assume_ (pure(A.is_full_array r.a));
  rewrite (exists_ (fun (s:(Seq.seq U8.t){Seq.length s == len}) -> A.pts_to r.a full_perm s) `star` pure(A.is_full_array r.a))
    as (rec_perm r);
  admit()
}
```
