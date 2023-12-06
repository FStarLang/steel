module GlobalStateTest

open Pulse.Lib.Mutex
open Pulse.Lib.GlobalState

open Pulse.Lib.Pervasives

module U32 = FStar.UInt32
module Box = Pulse.Lib.Box

assume val run_stt (#a:Type) (#q:a -> vprop) (f:stt a emp q) : a

noeq
type st = {
  x : Box.box U32.t;
  y : Box.box U32.t;
}

let st_vp (s:st) : vprop =
  (exists_ (fun (vx:U32.t) -> Box.pts_to s.x vx)) **
  (exists_ (fun (vy:U32.t) -> Box.pts_to s.y vy))

```pulse
fn mk_glob (_:unit)
  requires emp
  returns _:mutex st_vp
  ensures emp
{
  admit ()
}
```

let glob : global_state (mutex st_vp) =
  run_stt (mk mk_glob)

```pulse
fn sum_st (r:ref st)
  requires (exists (x:st). pts_to r x ** st_vp x)
  returns _:U32.t
  ensures (emp ** exists (x:st). pts_to r x ** st_vp x)
{
  admit ()
}
```

#push-options "--log_queries --fuel 2 --ifuel 2"
#restart-solver

```pulse
fn use_glob (_:unit)
  requires emp
  returns _:U32.t
  ensures emp
{
  let globr = get glob;
  let globv = !globr;
  let r = with_lock globv sum_st;
  put glob globr;
  r
}
```
