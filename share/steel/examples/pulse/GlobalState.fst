module GlobalState

open Steel.FractionalPermission
open Steel.ST.Util
open Steel.ST.Reference
open Steel.ST.SpinLock

open Pulse.Main
open Pulse.Steel.Wrapper

module U32 = FStar.UInt32
module W = Pulse.Steel.Wrapper

friend Pulse.Steel.Wrapper

#push-options "--fuel 0 --ifuel 0"

//
// The type of the state
//
// A reference whose permission is stored in the lock
//

type t = r:ref U32.t & lock (exists_ (fun n -> pts_to r full_perm n))

//
// Allocate a state instance
//
// The ascription on the last line is needed
// We should be able to fix it
//

```pulse
fn alloc (_:unit)
  requires emp
  returns _:t
  ensures emp
{
  let r = W.alloc #U32.t 0ul;
  let l = W.new_lock (exists_ (fun n -> pts_to r full_perm n));
  ((| r, l |) <: t)
}
```

//
// This is where we cheat a little bit and apply the alloc function
//   to create a global variable of state type
//
// It peeks beneath the stt abstraction to do so
//

let st : t = alloc () ()

//
// Read state
//

```pulse
fn read (_:unit)
  requires emp
  returns _:U32.t
  ensures emp
{
  let l = dsnd st;
  W.acquire #(exists_ (fun n -> pts_to (dfst st) full_perm n)) l;
  let n = !(dfst st);
  W.release #(exists_ (fun n -> pts_to (dfst st) full_perm n)) l;
  n
}
```


//
// Update state
//

```pulse
fn update (_:unit)
  requires emp
  ensures emp
{
  let l = dsnd st;
  W.acquire #(exists_ (fun n -> pts_to (dfst st) full_perm n)) l;
  dfst st := 1ul;
  W.release #(exists_ (fun n -> pts_to (dfst st) full_perm n)) l
}
```
