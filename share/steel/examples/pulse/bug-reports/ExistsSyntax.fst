module ExistsSyntax
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util
open Pulse.Steel.Wrapper
open Steel.ST.Reference
open FStar.Ghost
module U8 = FStar.UInt8
module R = Steel.ST.Reference

```pulse
fn some_function (r0:ref U8.t) (r1:ref U8.t) (#s:erased U8.t)
   requires 
      R.pts_to r0 full_perm s **
      exists (s1:U8.t). R.pts_to r1 full_perm s1
   ensures
        emp
{
    let x = !r0;
    let y = !r1;
    admit()
}
```


```pulse
fn call_some_function (r0:ref U8.t) (r1:ref U8.t) (#s0:erased U8.t) (#s1:erased U8.t)
   requires
     R.pts_to r0 full_perm s0 **
     R.pts_to r1 full_perm s1
   ensures
     emp
{
    some_function r0 r1;
    ()
}
```
