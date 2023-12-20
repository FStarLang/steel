module Pulse.Lib.Par.Pledge

open Pulse.Lib.Pervasives

val pledge (opens:inames) (f:vprop) (v:vprop) : vprop

let pledge_any (f:vprop) (v:vprop) : vprop =
  exists* is. pledge is f v

```pulse
ghost val
fn pledge_sub_inv (os1:inames) (os2: (os2:inames{inames_subset os1 os2})) (f:vprop) (v:vprop)
  requires pledge os1 f v
  ensures pledge os2 f v
```
  
(* Anything that holds now holds in the future too. *)
```pulse
ghost val
fn return_pledge (os:inames) (f:vprop) (v:vprop)
  requires v
  ensures pledge os f v
```

```pulse
ghost val
fn make_pledge (os:inames) (f:vprop) (v:vprop) (extra:vprop)
  (k : (unit -> stt_ghost unit os (f ** extra) (fun _ -> f ** v)))
  requires extra
  ensures pledge os f v
```

```pulse
ghost val
fn redeem_pledge (os:inames) (f:vprop) (v:vprop)
  requires f ** pledge os f v
  ensures f ** v
  opens os
```

// Unclear how useful/convenient this is
```pulse
ghost val
fn bind_pledge (#os:inames) (#f:vprop) (#v1:vprop) (#v2:vprop)
    (extra:vprop)
    (k : (unit -> stt_ghost unit os (f ** extra ** v1) (fun () -> f ** pledge os f v2)))
  requires pledge os f v1 ** extra
  ensures pledge os f v2
```

(* Weaker variant, the proof does not use f. It's implemented
by framing k with f and then using the above combinator. Exposing
only in case it's useful for inference. *)
```pulse
ghost val
fn bind_pledge' (#os:inames) (#f:vprop) (#v1:vprop) (#v2:vprop)
    (extra:vprop)
    (k : (unit -> stt_ghost unit os (extra ** v1) (fun () -> pledge os f v2)))
  requires pledge os f v1 ** extra
  ensures pledge os f v2
```

```pulse
ghost val
fn join_pledge (#os:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  requires pledge os f v1 ** pledge os f v2
  ensures pledge os f (v1 ** v2)
```

```pulse
ghost val
fn split_pledge (#os:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  requires pledge os f (v1 ** v2)
  returns i:iname
  ensures pledge (add_iname os i) f v1 ** pledge (add_iname os i) f v2
```

```pulse
ghost val
fn rewrite_pledge (#os:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  (k : (unit -> stt_ghost unit os v1 (fun _ -> v2)))
  requires pledge os f v1
  ensures pledge os f v2
```