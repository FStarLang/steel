module Global
open Pulse.Main
open Pulse.Steel.Wrapper
module W = Pulse.Steel.Wrapper
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
open Steel.ST.Array
module A = Steel.ST.Array
module R = Steel.ST.Reference
module US = FStar.SizeT
open Array 

(* mutate global vars that are assumed *)

assume val r : R.ref int

```pulse 
fn init_global_ref (_:unit) 
  requires exists v. R.pts_to r full_perm v
  ensures exists v. R.pts_to r full_perm v
{
  r := 0;
  ()
}
```

assume val l : l:US.t{US.v l > 0}
assume val a : A.array int
assume val s : s:Ghost.erased (Seq.seq int){Seq.length s = US.v l}

```pulse 
fn init_global_array (_:unit) 
  requires A.pts_to a full_perm s
  ensures exists s_. A.pts_to a full_perm s_
{
  (a.(0sz) <- 0);
  with s_. assert A.pts_to a full_perm s_;
  ()
}
```

(* Initialize global variables by calling Pulse.Steel.Wrapper functions 

Want to initialize global variables using steel wrapper functions
but they return stt types. 

To do this, we either need to be able to write global vars within Pulse's scope:

```pulse
let r2 : R.ref int = W.alloc 0
```

or to be able to extract the underlying type from the stt type in the FStar
let binding. 

*)

[@@expect_failure]
(* 
Returns 
  stt (R.ref int) emp (fun r -> R.pts_to r full_perm 0)
Instead of 
  R.ref int
*)
let r2 : R.ref int = W.alloc 0

[@@expect_failure]
(* 
Returns 
  stt (A.array int) 
      (requires emp)
      (ensures fun a ->
        A.pts_to a full_perm (Seq.create (US.v l) 0) `star`
        pure (A.length a == US.v l /\ A.is_full_array a))
Instead of
  A.array int
*)
let a2 : A.array int = W.new_array 0 l 