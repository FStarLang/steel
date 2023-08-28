module FlippableInv

open Pulse.Lib.Pervasives
open Promises.Temp
module GR = Pulse.Lib.GhostReference

(*
Random note about fixpoints:

let rec fix_1 (#a : Type) (#b : a -> Type)
  (ff : (x:a -> (y:a{y << x} -> Tot (b y)) -> Tot (b x)))
  : x:a -> Tot (b x)
  = fun x -> ff x (fix_1 ff)

let rec fix_ghost_1 (#a : Type0) (#b : a -> Type0)
  (ff : (x:a -> (y:a{y << x} -> GTot (b y)) -> GTot (b x)))
  : x:a -> GTot (b x)
  = fun x -> ff x (fix_ghost_1 ff)

let rec fix_stt_ghost_1 (#a : Type) (#b : a -> Type) (#pre : a -> vprop) (#post : (x:a -> b x -> vprop))
  (ff : (x:a -> (y:a{y << x} -> stt_ghost (b y) emp_inames (pre y) (post y)) -> stt_ghost (b x) emp_inames (pre x) (post x)))
  : x:a -> stt_ghost (b x) emp_inames (pre x) (post x)
  //= fun x -> ff x (fix_stt_ghost_1 ff)
  = fix_1 #a #(fun x -> stt_ghost (b x) emp_inames (pre x) (post x)) ff

let rec fix_stt_1 (#a : Type) (#b : a -> Type) (#pre : a -> vprop) (#post : (x:a -> b x -> vprop))
  (ff : (x:a -> (y:a{y << x} -> stt (b y) (pre y) (post y)) -> stt (b x) (pre x) (post x)))
  : x:a -> stt (b x) (pre x) (post x)
  //= fun x -> ff x (fix_stt_1 ff)
  = fix_1 #a #(fun x -> stt (b x) (pre x) (post x)) ff
  *)

let finv_p (p:vprop) (r : GR.ref bool) : vprop =
  exists_ (fun (b:bool) -> GR.pts_to r #one_half b ** (if b then p else emp))

type finv (p:vprop) = r:GR.ref bool & inv (finv_p p r)

let off #p (fi : finv p) : vprop = GR.pts_to (dfst fi) #one_half false
let on  #p (fi : finv p) : vprop = GR.pts_to (dfst fi) #one_half true

#set-options "--error_contexts true"

```pulse
fn __mk_finv (p:vprop)
   requires emp
   returns f:(finv p)
   ensures off f
{
   let r : GR.ref bool = GR.alloc false;
   GR.share2 # _#emp_inames r;
   rewrite emp
        as `@(if false then p else emp);
   fold finv_p p r;
   let i : inv (finv_p p r) = new_invariant' #emp_inames (finv_p p r);
   let i : inv (finv_p p r) = i;
   let fi : finv p = Mkdtuple2 #(GR.ref bool) #(fun r -> inv (finv_p p r)) r i;
   rewrite (GR.pts_to r #one_half false)
        as (GR.pts_to (dfst fi) #one_half false);
   fold (off #p fi);
   fi
}
```
let mk_finv = __mk_finv

let unref2 (#p:vprop) (i : inv p) : inv p = i

```pulse
fn __flip_on (#p:vprop) (fi : finv p)
   requires off fi ** p
   ensures on fi
{
  open Pulse.Lib.GhostReference;
  let r = dfst fi;
  let i : inv (finv_p p r) = dsnd fi;
  with_invariants (unref2 i) {
    unfold off fi;
    unfold finv_p p r;
    with bb.
      assert (GR.pts_to r #one_half bb ** `@(if bb then p else emp));

    rewrite (GR.pts_to (dfst fi) #one_half false)
         as (GR.pts_to r #one_half false);

    GR.gather2 #bool #emp_inames
      r
      #false #bb;

    rewrite `@(if bb then p else emp)
         as emp;
         
    r := true;
    
    GR.share2 #_ #emp_inames r;
    
    rewrite (GR.pts_to r #one_half true)
         as (GR.pts_to (dfst fi) #one_half true);
         
    rewrite p
         as `@(if true then p else emp);
         
    fold finv_p p r;

    fold (on fi);

    ()
  }
}
```
let flip_on = __flip_on

```pulse
fn __flip_off (#p:vprop) (fi : finv p)
   requires on fi
   ensures off fi ** p
{
  open Pulse.Lib.GhostReference;
  let r = dfst fi;
  let i : inv (finv_p p r) = dsnd fi;
  with_invariants (unref2 i) {
    unfold on fi;
    unfold finv_p p r;

    with bb.
      assert (GR.pts_to r #one_half bb ** `@(if bb then p else emp));

    rewrite (GR.pts_to (dfst fi) #one_half true)
         as (GR.pts_to r #one_half true);

    GR.gather2 #bool #emp_inames
      r
      #true #bb;

    rewrite `@(if bb then p else emp)
         as p;
         
    r := false;
    
    GR.share2 #_ #emp_inames r;
    
    rewrite (GR.pts_to r #one_half false)
         as (GR.pts_to (dfst fi) #one_half false);
         
    rewrite emp
         as `@(if false then p else emp);
         
    fold finv_p p r;

    fold (off fi);

    ()
  }
}
```

let flip_off = __flip_off
