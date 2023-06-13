module ArrayTests
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Array
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module US = FStar.SizeT


#push-options "--using_facts_from '* ArrayTests -Steel Steel.ST.Array -FStar.Tactics -FStar.Reflection'"

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

//this is not a recommended way to do this, since s is not erased, but it works
```pulse
fn read_at_offset_0 (#t:Type0) (a:array t) (i:US.t) (#p:perm) (#s:Seq.seq t)
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

```pulse
fn read_at_offset_poly (#t:Type0) (a:array t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq t))
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

//Error message is poor as usual
//But, this type is genuinely incorrect, since the return type does not assume
//the validity of the pure conjuncts in the requires
//so the sequence indexing there cannot be proven to be safe
//Maybe we should find a way to allow the pure conjuncts to be assumed in the returns
//Megan correctly remarks that this is unintuitive ... let's see if we can fix it
[@@expect_failure]
```pulse
fn read_at_offset_refine_fail (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s `star` pure (US.v i < A.length a))
   returns x: (x:U32.t { Seq.length s == A.length a /\
                         x == Seq.index s (US.v i)})
   ensures (
      A.pts_to a p s
   )
{ 
   let x = a.(i);
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
   let x = a.(i);
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
   let x = a.(i);
   (x <: (x:U32.t { Seq.length s == A.length a /\
                    US.v i < A.length a /\
                    x == Seq.index s (US.v i)}))
} 
```

```pulse
fn write_at_offset (#t:Type0) (a:array t) (i:US.t) (v:t)
                   (#s:(s:Ghost.erased (Seq.seq t) {US.v i < Seq.length s}))
   requires (A.pts_to a full_perm s)
   ensures (A.pts_to a full_perm (Seq.upd s (US.v i) v))
{
   (a.(i) <- v)
}
```

```pulse
fn write_at_offset_refine_post (#t:Type0) (a:array t) (i:US.t) (v:t) (#s:Ghost.erased (Seq.seq t))
   requires (A.pts_to a full_perm s `star`
               pure (US.v i < Seq.length s))
   returns a: (a:array t { US.v i < Seq.length s })
   ensures (A.pts_to a full_perm (Seq.upd s (US.v i) v))
{
   (a.(i) <- v);
   (a <: (a:array t { US.v i < Seq.length s }))
}
```

```pulse
fn write_then_read (#t:Type0) (a:array t) (i:US.t) (v:t)
                   (#s:(s:Ghost.erased (Seq.seq t) {US.v i < Seq.length s}))
   requires (A.pts_to a full_perm s `star`
             pure (US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a full_perm (Seq.upd s (US.v i) v) `star`
      pure (US.v i < Seq.length (Seq.upd s (US.v i) v) /\
            x == Seq.index (Seq.upd s (US.v i) v) (US.v i))
   )
{
   (a.(i) <- v);
   let x = a.(i);
   x
} 
```

```pulse
fn write_then_read_twice (#t:Type0) (a:array t) (i:US.t) (v1 v2:t)
                         (#s:(s:Ghost.erased (Seq.seq t) {US.v i < Seq.length s}))
   requires (A.pts_to a full_perm s `star`
             pure (US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a full_perm (Seq.upd (Seq.upd s (US.v i) v1) (US.v i) v2) `star`
      pure (US.v i < Seq.length (Seq.upd (Seq.upd s (US.v i) v1) (US.v i) v2) /\
            x == Seq.index (Seq.upd (Seq.upd s (US.v i) v1) (US.v i) v2) (US.v i))
   )
{
   let x1 = write_then_read a i v1;
   let x2 = write_then_read a i v2;
   x2
} 
```

```pulse
fn write_then_read_twice_neq (#t:Type0) (a:array t) (i:US.t) (v1 v2:t)
                             (#s:(s:Ghost.erased (Seq.seq t) {US.v i < Seq.length s}))
   requires (A.pts_to a full_perm s `star`
             pure (US.v i < Seq.length s /\
                  ~(v1 == v2)))
   returns p: t&t
   ensures (
      A.pts_to a full_perm (Seq.upd (Seq.upd s (US.v i) v1) (US.v i) v2) `star`
      pure (US.v i < Seq.length (Seq.upd (Seq.upd s (US.v i) v1) (US.v i) v2) /\
            snd p == Seq.index (Seq.upd (Seq.upd s (US.v i) v1) (US.v i) v2) (US.v i) /\
            ~(fst p == snd p))
   )
{
   let x1 = write_then_read a i v1;
   let x2 = write_then_read a i v2;
   (x1,x2)
} 
```

// assume
// val free_array (a: A.array U32.t)
//   : stt unit
//     (fun _ -> (A.pts_to a full_perm) `star` pure (A.is_full_array a))
//     (fun _ -> emp)

```pulse
fn alloc_then_free (n:US.t)
  requires emp
  ensures emp
{
  let a = new_array 0ul n;
  free_array a;
}
```

let sorted (s0 s:Seq.seq U32.t) =
   (forall (i:nat). i < Seq.length s - 1 ==> U32.v (Seq.index s i) <= U32.v (Seq.index s (i + 1))) /\
   (forall (i:nat). i < Seq.length s0 ==> (exists (j:nat). j < Seq.length s /\ U32.v (Seq.index s0 i) == U32.v (Seq.index s j))) /\
   (Seq.length s0 = Seq.length s)


open FStar.UInt32
// #push-options "--query_stats"

```pulse
fn sort3 (a:array U32.t)
         (#s:(s:Ghost.erased (Seq.seq U32.t) {Seq.length s == 3}))
   requires (A.pts_to a full_perm s)
   ensures 
      exists s'. (
         A.pts_to a full_perm s' `star`
         pure (sorted s s')
      )
{
   let x = a.(0sz);
   let y = a.(1sz);
   let z = a.(2sz);
   if (x >^ y) 
   {
      if (y >^ z)
      {
         (a.(0sz) <- z);
         (a.(1sz) <- y);
         (a.(2sz) <- x);
         ()
      }
      else {
         if (x >^ z)
         {
            (a.(0sz) <- y);
            (a.(1sz) <- z);
            (a.(2sz) <- x);
            ()
         }
         else
         {
            (a.(0sz) <- y);
            (a.(1sz) <- x);
            (a.(2sz) <- z);
            ()  
         }     
      }
   }
   else {
      if (y >^ z) {
         if (x >^ z) {
            (a.(0sz) <- z);
            (a.(1sz) <- x);
            (a.(2sz) <- y);
            ()
         }
         else {
            (a.(0sz) <- x);
            (a.(1sz) <- z);
            (a.(2sz) <- y);
            ()
         }
      }
      else {
         (a.(0sz) <- x);
         (a.(1sz) <- y);
         (a.(2sz) <- z);
         ()
      }
   }
}
```

//Pulse does not yet implement join point inference
[@@expect_failure [228]]
```pulse
fn sort3_alt (a:array U32.t)
             (#s:(s:Ghost.erased (Seq.seq U32.t) {Seq.length s == 3}))
   requires (A.pts_to a full_perm s)
   ensures 
      exists s'. (
         A.pts_to a full_perm s' `star`
         pure (sorted s s')
      )
{
   let mut x = a.(0sz);
   let mut y = a.(1sz);
   let mut z = a.(2sz);
   let vx = !x;
   let vy = !y;
   if (vy <^ vx) 
   {
      x := vy;
      y := vx;
   };
   let vx = !x;
   let vz = !z;
   if (vz <^ vx)
   {
      x := vz;
      z := vx;
   };
   let vy = !y;
   let vz = !z;
   if (vz <^ vy)
   {
      y := vz;
      z := vy;
   };
   (a.(0sz) <- x);
   (a.(1sz) <- y);
   (a.(2sz) <- z);
   ()
}
```

```pulse
fn swap (r1 r2:ref U32.t)
        (#n1 #n2:erased U32.t)
  requires 
     (pts_to r1 full_perm n1 `star`
      pts_to r2 full_perm n2)
  ensures
     (pts_to r1 full_perm n2 `star`
      pts_to r2 full_perm n1)
{
  let x = !r1;
  let y = !r2;
  r1 := y;
  r2 := x
}
```

let my_sorted (s:Seq.seq U32.t) =
  forall (i:nat). i < Seq.length s - 1 ==> U32.v (Seq.index s i) <= U32.v (Seq.index s (i + 1))

```pulse 
fn insert_into_sorted (a:array U32.t) (l:(l:nat{A.length a = l})) (#s:Ghost.erased (Seq.seq U32.t))
	requires (A.pts_to a full_perm s `star`
						pure (A.length a = Seq.length s /\
									// my_sorted (Seq.slice s 0 (A.length a - 1))))
									my_sorted (Seq.slice s 0 (A.length a))))
	returns a:array U32.t
	ensures 
		exists s'. (
				A.pts_to a full_perm s' `star`
        pure (my_sorted s')
    )
{
	let mut j = l - 1;
	// while (let vj = !j; (vj > 0 /\ a.(vj-1) > a.(vj)))
	while (let vj = !j; (vj > 0))
	invariant b. exists vj. (
      pts_to j full_perm vj `star`
      pure (0 <= vj /\
            vj <= l - 1 /\
            my_sorted (Seq.slice s (vj-1) l) /\
            // b == (vj > 0 /\ a.(vj-1) > a.(vj)))
            b == (vj > 0))
  )
  {
    let vj = !j;
    // swap a.(vj-1) a.(vj);
    j := vj - 1
  };
  a
}
```

(*
```pulse
fn isort (a:array U32.t) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a full_perm s)
   ensures 
      exists s'. (
         A.pts_to a full_perm s' `star`
         pure (sorted s s')
      )
{
   let mut i = 1;
   while (let vi = !i; (vi < A.length a))
   invariant b. exists vi s'. (
      pts_to i full_perm vi `star`
      A.pts_to a full_perm s' `star`
      pure (1 <= vi /\
            vi <= A.length a /\
            sorted (Seq.slice s 0 vi) s' /\
            b == (vi < A.length a))
   )
   {
      let mut j = !i;
      while (let vj = !j; (vj > 0 /\ a.(vj-1) > a.(vj)))
      invariant b. exists vj. (
         pts_to j full_perm vj `star`
         pure (0 <= vj /\
               vj <= i /\
               b == (vj > 0 /\ a.(vj-1) > a.(vj)))
      )
      {
         let vj = !j;
         swap a.(vj-1) a.(vj);
         j := vj - 1
      };
      let vi = !i;
      i := vi + 1
   };
}
```
*)