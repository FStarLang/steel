module MatchBasic

#set-options "--warn_error -249"
#set-options "--error_contexts true"

module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
open Pulse.Steel.Wrapper

```pulse
fn test1 (n:nat)
  requires emp
  returns r:int
  ensures emp
{
  (* let v = n; *)
  match n {
    0 -> { 1 }
    _ -> { 0 }
  }
}
```

```pulse
fn test2 (n:nat)
  requires emp
  returns r:int
  ensures emp
{
  let v = n;
  match n {
    0 -> { 1 }
    x -> { x }
  }
}
```

```pulse
fn test3 (n:nat)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    0 -> { 1 }
    x -> { let y = x+1; y }
  }
}

```

// FIXME: Need to qualifiy the constructors or otherwise they desugar to
// the (not yet in scope) type below.
```pulse
fn test3_5 (n:option int) (z:bool)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    Pervasives.None -> { (-1) }
    Pervasives.Some x -> { x }
  }
}
```

noeq
type optionint =
  | None
  | Some of int

```pulse
fn test4 (n:optionint) (z:bool)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    MatchBasic.None -> { 0 }
    MatchBasic.Some x -> { x }
  }
}
```

```pulse
fn test5 (n:option int) (z:bool)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    Pervasives.None -> { (-1) }
    Pervasives.Some x -> { x }
  }
}
```
