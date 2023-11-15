module Demo.MultiplyByRepeatedAddition
open Pulse.Lib.Pervasives
open FStar.UInt32
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"
#set-options "--ext 'pulse:rvalues' --split_queries always"
#set-options "--z3rlimit 40"

module U32 = FStar.UInt32
open FStar.Mul
let rec multiply (x y:nat) : z:nat { z == x * y} =
    if x = 0 then 0
    else multiply (x - 1) y + y

```pulse
fn mult (x y:nat)
    requires emp
    returns z:nat
    ensures pure (z == x * y)
{
    let mut ctr = 0;
    let mut acc = 0;
    while ((ctr < x))
    invariant b.
    exists c a.
        pts_to ctr c **
        pts_to acc a **
        pure (a == (c * y) /\
              c <= x /\
              b == (c < x))
    {
        acc := acc + y;
        ctr := ctr + 1;
    };
    acc
}
```

open Pulse.Lib.BoundedIntegers
```pulse
fn mult32 (x y:U32.t)
    requires pure (fits #U32.t (v x * v y))
    returns z:U32.t
    ensures pure (v z == v x * v y)
{  
    let mut ctr = 0ul;
    let mut acc = 0ul;
    while ((ctr < x))
    invariant b.
    exists c a.
        pts_to ctr c **
        pts_to acc a **
        pure (c <= x /\
              v a == (v c * v y) /\
              b == (c < x))
    {
        acc := acc + y;
        ctr := ctr + 1ul;
    };
    acc
}
```

open FStar.UInt32
let i (x:U32.t) : GTot int = U32.v x 
```pulse
fn mult32' (x y:U32.t)
    requires pure (i x * i y <= 0xffffffff)
    returns z:U32.t
    ensures pure (i z == i x * i y)
{  
    let mut ctr = 0ul;
    let mut acc = 0ul;
    while ((ctr <^ x))
    invariant b.
    exists c a.
        pts_to ctr c **
        pts_to acc a **
        pure (c <=^ x /\
              i a == (i c * i y) /\
              b == (c <^ x))
    {
        acc := acc +^ y;
        ctr := ctr +^ 1ul;
    };
    acc
}
```
