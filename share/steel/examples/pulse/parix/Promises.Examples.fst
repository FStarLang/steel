module Promises.Examples

open Pulse.Lib.Pervasives
open Promises

#set-options "--ext pulse:guard_policy=SMTSync"
(* Assuming invariants *)

[@@erasable]
assume val inv : vprop -> Type0

// should be ghost
assume val mk_inv : p:vprop -> stt (inv p) p (fun _ -> emp)

assume val with_inv
  (#a:Type0) (#pre : vprop) (#post : (a -> vprop))
  (#p:vprop)
  (i:inv p)
  ($f : unit -> stt_ghost a emp_inames (p ** pre) (fun r -> p ** post r))
  : stt_ghost a emp_inames pre post

assume val admit_ghost
  (#a:Type0) (#pre : vprop) (#post : (a -> vprop))
  (_:unit)
  : stt_ghost a emp_inames pre post

type abc = | A | B | C


let invp (b:ref abc) (y:ref int) =
  exists_ (fun (bb:abc) -> pts_to b #(half_perm full_perm) bb ** (if bb = B then pts_to y 42 else emp))

```pulse
fn test_aux (b : ref abc) (y : ref int)
  requires pts_to b #(half_perm full_perm) B ** invp b y
  ensures pts_to b #(half_perm full_perm) C ** pts_to y 42 ** invp b y
{
  unfold invp b y;
  with bb.
    assert (pts_to b #(half_perm full_perm) bb ** `@(if bb = B then pts_to y 42 else emp));

  assert (pts_to b #(half_perm full_perm) B);
  assert (pts_to b #(half_perm full_perm) bb);

  // Automate?
  pts_to_injective_eq #abc
        #(half_perm full_perm) #(half_perm full_perm)
        #B #bb
        b;

  // Automate?
  rewrite (pts_to b #(half_perm full_perm) bb)
       as (pts_to b #(half_perm full_perm) B);

  gather2 #abc #emp_inames b;

  // Should automate
  rewrite (pts_to b #(sum_perm (half_perm full_perm) (half_perm full_perm)) true)
       as (pts_to b true);

  assert (pts_to b #full_perm true);

  b := false;

  share b;

  rewrite emp
       as (`@(if false then pts_to y 42 else emp));

  intro_exists (fun (bb:bool) -> pts_to b #(half_perm full_perm) bb ** (if bb then pts_to y 42 else emp))
    false;

  fold invp b y;

  ()
}
```


(* Promising and redeeming in a single func *)
```pulse
fn test (b : ref bool) (y : ref int)
  requires pts_to b false ** pts_to y yy
  returns x:int
  ensures promise (pts_to b true) (pts_to y 42)
{
  assert (pts_to b false);
  share b;
  assert (pts_to b #(half_perm full_perm) false);
  assert (pts_to b #(half_perm full_perm) false ** emp);
  rewrite emp
       as `@(if false then pts_to y 42 else emp);
  assert (pts_to b #(half_perm full_perm) false ** `@(if false then pts_to y 42 else emp));
  assert (exists_ (fun (bb:bool) ->
             pts_to b #(half_perm full_perm) bb ** (if bb then pts_to y 42 else emp)));
  let i = mk_inv (exists_ (fun (bb:bool) ->
             pts_to b #(half_perm full_perm) bb ** (if bb then pts_to y 42 else emp)));
  y := 42;
  make_promise
    (pts_to b #(half_perm full_perm) true)
    (pts_to y 42)
    emp
    (fun () -> with_inv
                 #unit
                 #(pts_to b true ** emp)
                 #(fun () -> pts_to b false ** pts_to y 42)
                 #(exists_ (fun (bb:bool) -> pts_to b #(half_perm full_perm) bb ** (if bb then pts_to y 42 else emp)))
               i
               (fun () -> test_aux b y)
  );
  admit()
//   admit()
}
```