module FlippableInv

open Pulse.Lib.Pervasives
open Promises.Temp
module GR = Pulse.Lib.GhostReference

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
