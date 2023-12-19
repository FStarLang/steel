module Pulse.Lib.Mutex

open Pulse.Lib.Core
open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock

noeq
type mutex (#a:Type0) (p:a -> vprop) = {
  a_ref : ref a;
  lock : lock (exists* v. pts_to a_ref v ** p v)
}

```pulse
fn new_mutex' (#a:Type0) (p:(a -> vprop)) (x:a)
  requires p x
  returns _:mutex p
  ensures emp
{
  let a_ref = alloc x;
  let lock = new_lock (exists* v. pts_to a_ref v ** p v);
  let m = { a_ref; lock };
  m
}
```

let new_mutex = new_mutex'

type mutex_guard a = ref a 
let mutex_guard_vp #_ p m = exists* v. pts_to m v ** p v

let is_guard_for_lock #_ #_ mg m = mg == m.a_ref

```pulse
fn mutex_lock' (#a:Type0) (#p:(a -> vprop)) (m:mutex p)
  requires emp
  returns mg:mutex_guard a
  ensures mutex_guard_vp p mg ** pure (mg `is_guard_for_lock` m)
{
  acquire m.lock;
  fold (mutex_guard_vp p m.a_ref);
  m.a_ref
}
```

let mutex_lock = mutex_lock'

let mutex_guard_to_ref #a mg = mg

```pulse
ghost
fn mg_vp_pts_to' (#a:Type0) (p:(a -> vprop)) (mg:mutex_guard a)
  requires mutex_guard_vp p mg
  ensures exists* v. pts_to (mutex_guard_to_ref mg) v ** p v
{
  unfold (mutex_guard_vp p mg);
  with v. rewrite (pts_to mg v)
               as (pts_to (mutex_guard_to_ref mg) v);
}
```

let mg_vp_pts_to = mg_vp_pts_to'

```pulse
ghost
fn pts_to_mg_vp' (#a:Type0) (p:(a -> vprop)) (mg:mutex_guard a)
  requires exists* v. pts_to (mutex_guard_to_ref mg) v ** p v
  ensures mutex_guard_vp p mg
{
  with v. rewrite (pts_to (mutex_guard_to_ref mg) v)
               as (pts_to mg v);
  fold (mutex_guard_vp p mg)
}
```

let pts_to_mg_vp = pts_to_mg_vp'

```pulse
fn mutex_unlock' (#a:Type0) (#p:(a -> vprop)) (m:mutex p) (mg:mutex_guard a)
  requires mutex_guard_vp p mg ** pure (mg `is_guard_for_lock` m)
  ensures emp
{
  unfold (mutex_guard_vp p mg);
  with v. rewrite (pts_to mg v)
               as (pts_to m.a_ref v);
  release m.lock
}
```

let mutex_unlock = mutex_unlock'
