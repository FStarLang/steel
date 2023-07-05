module SpinLock
open Pulse.Main
open Pulse.Steel.Wrapper
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
module R = Steel.ST.Reference
#push-options "--ide_id_info_off"

(* this works *)
```pulse
fn lock_ref (r:R.ref int) (#v_:Ghost.erased int)
  requires R.pts_to r full_perm v_
  ensures exists v. R.pts_to r full_perm v
{
  let my_lock = new_lock (exists_ (fun v -> R.pts_to r full_perm v));
  acquire #(exists_ (fun v -> R.pts_to r full_perm v)) my_lock;
  ()
}
```


(* 
  pulse fails to instantiate the existential var in
  the post condition
*)
[@@expect_failure]
```pulse
fn create_and_lock_ref (_:unit)
  requires emp
  returns r:R.ref int
  ensures exists v. R.pts_to r full_perm v
{
  let mut r = 0;
  let my_lock = new_lock (exists_ (fun v -> R.pts_to r full_perm v));
  acquire #(exists_ (fun v -> R.pts_to r full_perm v)) my_lock;
  r
}
```


let ref_prop (r:R.ref int) : vprop
  = exists_ (fun v -> R.pts_to r full_perm v)

(*
  pulse fails to unify (ref_prop r) with (R.pts_to r full_perm v_)
  on line 55
*)
[@@expect_failure]
```pulse
fn lock_ref_refactor (r:R.ref int) (#v_:Ghost.erased int)
  requires R.pts_to r full_perm v_
  ensures exists v. R.pts_to r full_perm v
{
  let my_lock = new_lock (ref_prop r);
  acquire #(ref_prop r) my_lock;
  ()
}
```
