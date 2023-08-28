module Invariant


open Pulse.Lib.Pervasives
open Pulse.Lib.Reference

```pulse
fn package (r:ref int)
   requires pts_to r 123
   returns i : inv (pts_to r 123)
   ensures emp
{
  let i : inv (pts_to r 123) =
    new_invariant' #emp_inames (pts_to r 123);
  i
}
```

// Incredibly basic  with_invariant test
// (and bogus, since it's in stt and the body is not atomic)
```pulse
fn test2 (_:unit)
  requires emp
  returns v:(v:int{v == 2})
  ensures emp
{
  let r = alloc 123;
  let i = package r;
  with_invariants i ensures pure True {
    r := 124;
    r := 123;
    ()
  };
  2
}
```