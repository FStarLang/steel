module SpinLock
open Pulse.Main
open Pulse.Steel.Wrapper
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
module R = Steel.ST.Reference
module L = Steel.ST.SpinLock
#push-options "--ide_id_info_off"

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


let ref_prop (r:R.ref int) : vprop
  = exists_ (fun v -> R.pts_to r full_perm v)

```pulse
fn lock_ref_refactor (r:R.ref int)
  requires ref_prop r
  returns l:L.lock (ref_prop r)
  ensures emp
{
  let my_lock = new_lock (ref_prop r);
  acquire #(ref_prop r) my_lock;
  release #(ref_prop r) my_lock;
  my_lock
}
```

