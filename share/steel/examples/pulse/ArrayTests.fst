module ArrayTests
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module US = FStar.SizeT


#push-options "--using_facts_from 'Prims FStar.Pervasives FStar.Ghost ArrayTests'"

```pulse
fn array_of_zeroes (n:US.t)
   requires emp
   returns a: array U32.t
   ensures (
    A.pts_to a full_perm (Seq.create (US.v n) 0ul) `star`
    pure (is_full_array a /\ A.length a == US.v n)
  )
{
   let a = new_array 0ul n;
   a
}
```

//this fails due to some reveal/hide confusion on the precondition of a.(i)
[@@expect_failure]
```pulse
fn read_at_offset (#t:Type0) (a:array t) (i:US.t) (#p:perm) (#s:Seq.seq t)
   requires (A.pts_to a p s `star`
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a p s `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{
   let x = a.(i);
   x
} 
```

//this fails due to a weird core typing error Seq.seq U32.t </: Seq.seq U32.t
[@@expect_failure]
```pulse
fn read_at_offset (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s `star`
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:U32.t
   ensures (
      A.pts_to a p s `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{
   let x = a.(i);
   x
} 
```

assume
val test_array_access
  (#t: Type)
  (a: A.array t)
  (i: US.t)
  (#s: Ghost.erased (Seq.seq t) {US.v i < A.length a \/ US.v i < Seq.length s})
  (#p: perm)
: stt t
    (requires
      A.pts_to a p s)
    (ensures fun res ->
      A.pts_to a p s `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            res == Seq.index s (US.v i)))

```pulse
fn read_at_offset (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s `star`
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:U32.t
   ensures (
      A.pts_to a p s
     `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{ 
   let x = test_array_access a i;
   x
} 
```


```pulse
fn read_at_offset_poly (#t:Type0) (a:array t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq t))
   requires (A.pts_to a p s `star`
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a p s
     `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{ 
   let x = test_array_access a i;
   x
} 
```
//Error message is poor as usual
//But, this type is genuinely incorrect, since the return type does not assume
//the validity of the pure conjuncts in the requires
//so the sequence indexing there cannot be proven to be safe
//Maybe we should find a way to allow the pure conjuncts to be assumed in the returns
//Megan correctly remarks that this is unintuitive ... let's see if we can fix it
[@@expect_failure]
```pulse
fn read_at_offset_refine (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s `star` pure (US.v i < A.length a))
   returns x: (x:U32.t { Seq.length s == A.length a /\
                         x == Seq.index s (US.v i)})
   ensures (
      A.pts_to a p s
   )
{ 
   let x = test_array_access a i;
   (x <: (x:U32.t { Seq.length s == A.length a /\
                    US.v i < A.length a /\
                    x == Seq.index s (US.v i)}))
} 
```

//But if we hoist the pure payload into a refinement, then it can be used for typing throughout the spec & body
```pulse
fn read_at_offset_refine (a:array U32.t) (i:(i:US.t { US.v i < A.length a})) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s)
   returns x: (x:U32.t { Seq.length s == A.length a /\
                         x == Seq.index s (US.v i)})
   ensures (
      A.pts_to a p s
   )
{ 
   let x = test_array_access a i;
   (x <: (x:U32.t { Seq.length s == A.length a /\
                         x == Seq.index s (US.v i)}))
} 
```

```pulse
fn read_at_offset_refine2 (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s `star` pure (US.v i < A.length a))
   returns x: (x:U32.t { Seq.length s == A.length a /\
                         US.v i < A.length a /\
                         x == Seq.index s (US.v i)})
   ensures (
      A.pts_to a p s
   )
{ 
   let x = test_array_access a i;
   (x <: (x:U32.t { Seq.length s == A.length a /\
                    US.v i < A.length a /\
                    x == Seq.index s (US.v i)}))
} 
```