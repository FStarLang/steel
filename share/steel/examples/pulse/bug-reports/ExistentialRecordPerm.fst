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

(* 
  When the record permission does not involve existentially
  quantified variables, we can transfer array permissions into
  a record permission
*)

noeq
type my_rec = { a:A.array U8.t }
let mk_rec a = { a }

assume val s : Seq.seq U8.t

let rec_perm (r:my_rec) : vprop 
  = A.pts_to r.a full_perm s
  
```pulse
fn rewrite_record_perm(a: A.array U8.t)
  requires A.pts_to a full_perm s
  returns r:my_rec
  ensures rec_perm r
{
  let r = mk_rec a;
  rewrite (A.pts_to a full_perm s)
    as (rec_perm r);
  r
}
```

(* 
  When the record permission involves existentially quantified 
  variables, Pulse cannot figure out that whatever permissions 
  we have on a are also held on r.a
*)

let rec_perm_existential (r:my_rec) : vprop 
  = exists_ (fun s -> A.pts_to r.a full_perm s)

```pulse
fn rewrite_existential (a: A.array U8.t)
  requires exists s. A.pts_to a full_perm s
  returns r:my_rec
  ensures rec_perm_existential r
{
  let r = mk_rec a;
  // FIXME: Pulse cannot infer line 56 from line 55
  drop_ (exists_ (fun s -> A.pts_to a full_perm s));
  assume_ (exists_ (fun s -> A.pts_to r.a full_perm s));
  // -----
  rewrite (exists_ (fun s -> A.pts_to r.a full_perm s))
    as (rec_perm_existential r);
  r
}
```
