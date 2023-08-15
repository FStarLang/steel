module Assert
open Pulse.Lib.Pervasives

open Steel.Memory

// let pred a = (a -> vprop) // a is the type of the argument

// let smaller #a (p q: pred) = magic()

```pulse
fn test_assert (r0 r1: ref nat)
               (#p0 #p1:perm)
               (#v0:nat)
    requires 
        pts_to r0 #p0 v0 **
        (exists v1. pts_to r1 #p1 v1)
    ensures
        pts_to r0 #p0 v0 **
        (exists v1. pts_to r1 #p1 v1)
{
    //assert_ (pts_to r1 ?p1 ?v1); would be nice to have a version that also binds witnesses
    assert_ (pts_to r0 #p0 (v0 + 0));
    ()
}
```
