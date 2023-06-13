module Factorial
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper
open FStar.Mul

let rec fac (n:nat) : nat =
    if n = 0 then 1
    else n * fac (n-1)

```pulse
fn fac_imp (n:pos)
  requires emp
  returns r:int
  ensures pure (r == fac n)
{
  let mut acc = 1;
  let mut ctr = 1;
  while (let vctr = !ctr; (vctr < n))
  invariant b . exists vacc vctr. (
    pts_to acc full_perm vacc `star`
    pts_to ctr full_perm vctr `star`
    pure (1 <= vctr /\
          vctr <= n /\
          vacc == fac vctr /\
          b == (vctr < n))
  )
  {
    let vc = !ctr;
    let va = !acc;
    ctr := vc + 1;
    acc := (vc + 1) * va;
    ()
  };
  let r = !acc;
  r
}
```