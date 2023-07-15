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
fn test_par (r1 r2 r3:ref U32.t)
            (#n1 #n2 #n3:erased U32.t)
  requires 
    (pts_to r1 full_perm n1 **
     pts_to r2 full_perm n2 **
     pts_to r3 full_perm n3)
  ensures
    (pts_to r1 full_perm n1 **
     pts_to r2 full_perm 1ul **
     pts_to r3 full_perm 1ul)
{
  parallel
    requires (_) and (_)
    ensures  (_) and (_)
  {
    // context: A * B * C
     write r1 #n1 // Goes to C_ST
     //s1; // A -> A (frame B * C)
     //s2 // B -> B (frame A * C)

     // Algorithm:
     // 1. Check left branch with full context
     // 2. Extract common frame F from the typing derivation
     // 3. Remove this frame from the left
     // 4. Use this frame to type check right branch

     // exists v. (r -> v * B)
     // (exists v. r -> v) * B

(*
     Seq
     (Frame (B * C) (... s1...))
     (Frame (A * C) (... s2...))
    -->
    Frame C (
     Seq
     (Frame B (... s1...))
     (Frame A (... s2...)))

// Two lemmas needed
     Seq (Frame C ...) (Frame C ...)
     ==> Frame C (Seq ... ...)

     Frame (B * C) s
     ==> Frame C (Frame B s)
     *)

   }
  {
     r2 := 1ul;
     r3 := 1ul
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