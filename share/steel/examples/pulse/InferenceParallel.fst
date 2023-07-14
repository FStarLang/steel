module InferenceParallel
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
open Pulse.Steel.Wrapper

module U32 = FStar.UInt32

```pulse
fn write (r: ref U32.t) (#n: erased U32.t)
  requires 
    (pts_to r full_perm n)
  ensures
    (pts_to r full_perm n)
{
    let x = !r;
    r := x;
    ()
}
```


```pulse
fn test_par (r1 r2:ref U32.t)
            (#n1 #n2:erased U32.t)
  requires 
    (pts_to r1 full_perm n1 `star`
     pts_to r2 full_perm n2)
  ensures
    (pts_to r1 full_perm n1 `star`
     pts_to r2 full_perm 1ul)
{
  parallel
    requires (_) and (_)
    ensures  (_) and (_)
  {
     write r1 #n1 // Goes to C_ST
  }
  {
     r2 := 1ul
  };
  ()
}
```

(*
```pulse
fn test_par_2 (r0 r1: ref nat)
               (#v0:nat) (#v1:nat)
    requires 
        pts_to r0 full_perm v0 ** pts_to r1 full_perm v1
    ensures
        pts_to r0 full_perm (v0 + 1) ** pts_to r1 full_perm (v1 + 2)
{
    parallel
        requires (pts_to r0 full_perm v0) and (pts_to r1 full_perm v1)
        ensures (pts_to r0 full_perm 1) and (pts_to r1 full_perm 2)
    {
        //thread r0 1
        r0 := 1;
        ()
    }
    {
        //thread r1 2
        r1 := 2;
        ()
    }
}
```
*)