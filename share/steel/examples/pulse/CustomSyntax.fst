module CustomSyntax
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper


#push-options "--using_facts_from 'Prims FStar.Pervasives FStar.UInt FStar.UInt32 FStar.Ghost Pulse.Steel.Wrapper CustomSyntax'"

```pulse
fn test_write_10 (x:ref U32.t)
                 (#n:erased U32.t)
   requires pts_to x full_perm n
   ensures  pts_to x full_perm 0ul
{
    x := 1ul;
    x := 0ul;
}
```

```pulse
fn test_read (r:ref U32.t)
             (#n:erased U32.t)
             (#p:perm)
   requires pts_to r p n
   returns x : U32.t
   ensures (pts_to r p x `star` pure (x==n))
{
  let x = !r;
  x
}
```

```pulse
fn test_read_2 (r:ref U32.t)
             (#n:erased U32.t)
             (#p:perm)
   requires pts_to r p n
   returns x : (x:U32.t{x==n})
   ensures pts_to r p x
{
  let x = !r;
  (x<:(x:U32.t{x==n}))
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


```pulse
fn call_swap2 (r1 r2:ref U32.t)
              (#n1 #n2:erased U32.t)
   requires
      (pts_to r1 full_perm n1 `star`
       pts_to r2 full_perm n2)
   ensures
      (pts_to r1 full_perm n1 `star`
       pts_to r2 full_perm n2)
{
   swap r1 r2;
   swap r1 r2
}
```


```pulse
fn swap_with_elim_pure (r1 r2:ref U32.t) 
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

```pulse
fn elim_and_intro_pure_example (r:ref U32.t)
                      (#n1 #n2:erased U32.t)
   requires 
     (pts_to r full_perm n1 `star`
      pure (reveal n1 == reveal n2))
   ensures 
     (pts_to r full_perm n2 `star`
      pure (reveal n2 == reveal n1))
{
  ()
}
```


```pulse
fn if_example (r:ref U32.t)
              (n:(n:erased U32.t{U32.v (reveal n) == 1}))
              (b:bool)
   requires 
     pts_to r full_perm n
   ensures
     pts_to r full_perm (U32.add (reveal n) 2ul)
{
   let x = read_atomic r;
   if b
   {
     r := U32.add x 2ul
   }
   else
   {
     write_atomic r 3ul
   }
}
```


```pulse
fn elim_intro_exists2 (r:ref U32.t)
   requires 
     exists n. pts_to r full_perm n
   ensures 
     exists n. pts_to r full_perm n
{
  introduce exists n. pts_to r full_perm n with _
}
```


assume
val pred (b:bool) : vprop
assume
val read_pred (_:unit) (#b:erased bool)
    : stt bool (pred b) (fun r -> pred r)

```pulse
fn while_test_alt (r:ref U32.t)
  requires 
    exists b n.
      (pts_to r full_perm n `star`
       pred b)
  ensures 
    exists n. (pts_to r full_perm n `star`
              pred false)
{
  while (let x = read_pred(); x)
  invariant b . exists n. (pts_to r full_perm n `star` pred b)
  {
    ()
  }
}
```

```pulse
fn infer_read_ex (r:ref U32.t)
  requires
    exists n. pts_to r full_perm n
  ensures exists n. pts_to r full_perm n
{
  let x = !r;
  ()
}
```


```pulse
fn while_count2 (r:ref U32.t)
  requires exists (n:U32.t). (pts_to r full_perm n)
  ensures (pts_to r full_perm 10ul)
{
  open FStar.UInt32;
  while (let x = !r; (x <> 10ul))
  invariant b. 
    exists n. (pts_to r full_perm n `star`
          pure (b == (n <> 10ul)))
  {
    let x = !r;
    if (x <^ 10ul)
    {
      r := x +^ 1ul; 
      ()
    }
    else
    {
      r := x -^ 1ul;
      ()
    }
  };
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
    (pts_to r1 full_perm 1ul `star`
     pts_to r2 full_perm 1ul)
{
  parallel
  requires (pts_to r1 full_perm n1)
       and (pts_to r2 full_perm n2)
  ensures  (pts_to r1 full_perm 1ul)    
       and (pts_to r2 full_perm 1ul)
  {
     r1 := 1ul
  }
  {
     r2 := 1ul
  };
  ()
}
```

// A test for rewrite
let mpts_to (r:ref U32.t) (n:erased U32.t) : vprop = pts_to r full_perm n

```pulse
fn rewrite_test (r:ref U32.t)
                (#n:erased U32.t)
   requires (mpts_to r n)
   ensures  (mpts_to r 1ul)
{
  rewrite (mpts_to r n) 
       as (pts_to r full_perm n);
  r := 1ul;
  rewrite (pts_to r full_perm 1ul)
       as (mpts_to r 1ul)
}
```

```pulse
fn test_local (r:ref U32.t)
              (#n:erased U32.t)
   requires (pts_to r full_perm n)
   ensures  (pts_to r full_perm 0ul)
{
  let mut x = 0ul;
  let y = !x;
  r := y;
  introduce exists n. (pts_to x full_perm n) with _
}
```

```pulse
fn count_local (r:ref int) (n:int)
   requires (pts_to r full_perm (hide 0))
   ensures (pts_to r full_perm n)
{
  let mut i = 0;
  while
    (let m = !i; (m <> n))
  invariant b. exists m. 
    (pts_to i full_perm m `star`
     pure (b == (m <> n)))
  {
    let m = !i;
    i := m + 1;
    ()
  };
  let x = !i;
  r := x;
  introduce exists m. (pts_to i full_perm m) with _
}
```


let rec sum_spec (n:nat) : nat =
  if n = 0 then 0 else n + sum_spec (n - 1)

 
let zero : nat = 0

```pulse
fn sum (r:ref nat) (n:nat)
   requires exists i. (pts_to r full_perm i)
   ensures (pts_to r full_perm (sum_spec n))
{
   let mut i = zero;
   let mut sum = zero;
   introduce exists b' m' s'. (
     pts_to i full_perm m' `star`
     pts_to sum full_perm s' `star`
     pure (s' == sum_spec m' /\
           b' == (m' <> n)))
   with (zero <> n) _ _;
        
   while (let m = !i; (m <> n))
   invariant b . exists m s. (
     pts_to i full_perm m `star`
     pts_to sum full_perm s `star`
     pure (s == sum_spec m /\
           b == (m <> n)))
   {
     let m = !i;
     let s = !sum;
     i := (m + 1);
     sum := s + m + 1;
     introduce exists b' m' s'. (
       pts_to i full_perm m' `star`
       pts_to sum full_perm s' `star`
       pure (s' == sum_spec m' /\
             b' == (m' <> n)))
     with (m + 1 <> n) _ _
   };
   let s = !sum;
   r := s;
   introduce exists m. (pts_to i full_perm m) 
   with _;
   introduce exists s. (pts_to sum full_perm s)
   with _
}
```

```pulse
fn sum2 (r:ref nat) (n:nat)
   requires exists i. (pts_to r full_perm i)
   ensures (pts_to r full_perm (sum_spec n))
{
   let mut i = zero;
   let mut sum = zero;
   while (let m = !i; (m <> n))
   invariant b . exists m s. (
     pts_to i full_perm m `star`
     pts_to sum full_perm s `star`
     pure (s == sum_spec m /\ b == (m <> n)))
   {
     let m = !i;
     let s = !sum;
     i := (m + 1);
     sum := s + m + 1;
     ()
   };
   let s = !sum;
   r := s;
   ()
}
```

```pulse
fn if_then_else_in_specs (r:ref U32.t)
  requires (if true
            then pts_to r full_perm 0ul
            else pts_to r full_perm 1ul)
  ensures  (if true
            then pts_to r full_perm 1ul
            else pts_to r full_perm 0ul)
{
  // need this for typechecking !r on the next line,
  //   with inference of implicits
  rewrite (if true then pts_to r full_perm 0ul else pts_to r full_perm 1ul)
       as (pts_to r full_perm 0ul);
  let x = !r;
  r := U32.add x 1ul
}
```

```pulse
fn test_tot_let (r:ref U32.t)
  requires (pts_to r full_perm 0ul)
  ensures  (pts_to r full_perm 2ul)
{
  let x = 1ul;
  let y = 1ul;
  r := U32.add x y
}
```

// Ascriptions coming in the way
// ```pulse
// fn if_then_else_in_specs2 (r:ref U32.t) (b:bool)
//   requires (pts_to r full_perm (if b then 0ul else 1ul))
//   ensures (pts_to r full_perm (if b then 1ul else 2ul))
// {
//   let x = !r;
//   r := U32.add x 1ul
// }
// ```


```pulse
fn incr (x:nat)
  requires emp
  returns r : (r:nat { r > x })
  ensures emp
{
  let y = x + 1;
  ( y <: r:nat { r > x } )
}
```

```pulse
fn dummy_tuple (#t:Type0) (r:ref t) (#n:erased t) (#p:perm)
  requires pts_to r p n
  returns ret : t & U32.t
  ensures (pts_to r p (fst ret) `star` 
          pure (fst ret == n /\
                snd ret = 0ul))
{
  let x = !r;
  (x, 0ul)
}
```