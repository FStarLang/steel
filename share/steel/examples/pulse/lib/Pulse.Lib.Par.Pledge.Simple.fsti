module Pulse.Lib.Par.Pledge.Simple

open Pulse.Lib.Pervasives

(* In this this version of the pledge library, pledges
are not indexed by invariants. The actual invariants are existentially
quantified inside the Simple.pledge vprop, and we provide
effectful operations to manipulate them. *)

val pledge (f:vprop) (v:vprop) : vprop

(* Anything that holds now holds in the future too. *)
```pulse
ghost val
fn return_pledge (f:vprop) (v:vprop)
  requires v
  ensures pledge f v
```

(* The function proving a pledge can use any invariants. *)
```pulse
ghost val
fn make_pledge (#os:inames) (f:vprop) (v:vprop) (extra:vprop)
  (k : (unit -> stt_ghost unit os (f ** extra) (fun _ -> f ** v)))
  requires extra
  ensures pledge f v
```

(* Redeem is stateful *)
```pulse
val
fn redeem_pledge (f:vprop) (v:vprop)
  requires f ** pledge f v
  ensures f ** v
```

// Unclear how useful/convenient this is
```pulse
ghost val
fn bind_pledge (#os:inames) (#f:vprop) (#v1:vprop) (#v2:vprop)
    (extra:vprop)
    (k : (unit -> stt_ghost unit os (f ** extra ** v1) (fun () -> f ** pledge f v2)))
  requires pledge f v1 ** extra
  ensures pledge f v2
```

(* Weaker variant, the proof does not use f. It's implemented
by framing k with f and then using the above combinator. Exposing
only in case it's useful for inference. *)
```pulse
ghost val
fn bind_pledge' (#os:inames) (#f:vprop) (#v1:vprop) (#v2:vprop)
    (extra:vprop)
    (k : (unit -> stt_ghost unit os (extra ** v1) (fun () -> pledge f v2)))
  requires pledge f v1 ** extra
  ensures pledge f v2
```

```pulse
ghost val
fn join_pledge (#f:vprop) (v1:vprop) (v2:vprop)
  requires pledge f v1 ** pledge f v2
  ensures pledge f (v1 ** v2)
```

```pulse
ghost val
fn split_pledge (#f:vprop) (v1:vprop) (v2:vprop)
  requires pledge f (v1 ** v2)
  ensures pledge f v1 ** pledge f v2
```

```pulse
ghost val
fn rewrite_pledge (#os:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  (k : (unit -> stt_ghost unit os v1 (fun _ -> v2)))
  requires pledge f v1
  ensures pledge f v2
```
