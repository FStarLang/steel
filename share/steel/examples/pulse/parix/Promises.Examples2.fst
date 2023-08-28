module Promises.Examples2

open Pulse.Lib.Pervasives
open Promises.Temp.NoKeep

assume val b : ref bool
assume val y : ref (option int)

let pts_to_some #a (r : ref (option a)) (#[Tactics.exact (`full_perm)] p : perm) =
  exists_ (fun (v:a) -> pts_to r #p (Some v))

```pulse
fn prepare (_:unit)
   requires pts_to b bb ** pts_to y yy
   returns _:unit
   ensures promise (pts_to b #one_half true) (pts_to_some y #full_perm)
{
  admit()
}
```

let invp (b:ref abc) (y:ref int) =
  exists_ (fun (bb:abc) -> pts_to b #one_half bb ** (if bb = B then pts_to y 42 else emp))

```pulse
fn test_aux (b : ref abc) (y : ref int)
  requires pts_to b #one_half B ** invp b y
  ensures pts_to y 42 ** invp b y
{
  unfold invp b y;
  with bb.
    assert (pts_to b #one_half bb ** `@(if bb = B then pts_to y 42 else emp));

  assert (pts_to b #one_half B);
  assert (pts_to b #one_half bb);

  // Automate?
  pts_to_injective_eq #abc
        #one_half #one_half
        #B #bb
        b;

  assert (pts_to b #one_half (reveal (hide B)) ** pts_to b #one_half (reveal (hide B)));

  gather2 #abc #emp_inames b;

  b := C; // The only non-ghost step

  share2 #_ #emp_inames b;

  rewrite emp
       as (`@(if false then pts_to y 42 else emp));

  intro_exists (fun (bb:abc) -> pts_to b #one_half bb ** (if bb = B then pts_to y 42 else emp))
    C;

  assert (pts_to y 42);

  fold invp b y;
  drop_ (pts_to b #one_half C);

  ()
}
```

// ```pulse
// fn test_aux_with_inv (b : ref abc) (y : ref int) (i : inv (invp b y))
//   requires pts_to b #one_half B
//   ensures pts_to b #one_half C ** pts_to y 42
// {
//    with_invariants i {
//      test_aux b y
//    }
// }
// ```

let pts_to_b_or_c (b : ref abc) =
  exists_ (fun (v:abc) -> pts_to b #one_half v ** pure (B? v \/ C? v))

```pulse
fn test_aux_with_inv2 (b : ref abc) (y : ref int) (i : inv (invp b y))
  requires pts_to b #one_half B ** emp
  ensures pts_to y 42
{
   (* This would be a ghost read.. *)
   let v = !b;
   match v {
      B -> {
        with_invariants i ensures pts_to y 42
        {
          test_aux b y
        };
        ()
      }
   }
}
```

#set-options "--split_queries always"


(* Promising and redeeming in a single func *)
```pulse
fn test (b : ref abc) (y : ref int)
  requires pts_to b A ** pts_to y yy
  returns x:int
  ensures pts_to y 42
{
  share2 #_ #emp_inames b;
  assert (pts_to b #one_half A);
  assert (pts_to b #one_half A ** emp);

  rewrite emp
       as `@(if false then pts_to y 42 else emp);
  assert (pts_to b #one_half A ** `@(if A = B then pts_to y 42 else emp));

  assert (exists_ (fun (bb:abc) ->
             pts_to b #one_half bb ** (if bb = B then pts_to y 42 else emp)));

  fold invp b y;
  let i = new_invariant' #emp_inames (invp b y);

  let pp =
    make_promise
      (pts_to b #one_half B)
      (pts_to y 42)
      emp
      (fun () -> test_aux_with_inv2 b y i);

  y := 42;

  // Set b:=B, keeping the invariant.
  // FIXME: shouldn't have to talk about promise and y?
  with_invariants i ensures
     promise (pts_to b #one_half B) (pts_to y 42)
     //** pts_to y 42
     ** pts_to b #one_half B
  {
    unfold invp b y;
    assert (exists bb. pts_to b #one_half bb ** `@(if bb = B then pts_to y 42 else emp));
    with ba.
      assert (pts_to b #one_half ba ** `@(if ba = B then pts_to y 42 else emp));

    assert (pts_to b #one_half A);

    // Automate?
    pts_to_injective_eq #abc
          #one_half #one_half
          #A #ba
          b;

    assert (pure (ba == A));

    gather2 #_ #emp_inames b;
    b := B;
    share2 #_ #emp_inames b;

    assert (pts_to b #one_half B ** `@(if B = B then pts_to y 42 else emp));
    intro_exists (fun (bb:abc) -> pts_to b #one_half bb ** (if bb = B then pts_to y 42 else emp))
      B;
    fold (invp b y);
    assert (invp b y);
    assert (invp b y);
    assert (invp b y);

    // Pretty hard to find out to do this.
    rewrite (`@(if ba = B then pts_to y 42 else emp))
         as emp;

    assert (pts_to b #one_half B);

    assert (invp b y);
    ()
  };

  assert (pts_to b #one_half B);
  // fold (pts_to_b_or_c b);
  // assert (pts_to_b_or_c b);
  redeem_promise (pts_to b #one_half B) (pts_to y 42);

  assert (pts_to y 42);
  // drop_ (pts_to_b_or_c b);

  1234 
}
```
