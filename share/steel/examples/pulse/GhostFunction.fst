module GhostFunction
open Pulse.Lib.Pervasives
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference

assume val f (x:int) : GTot int

//
// calling GTot functions in ghost functions is ok
//
```pulse
ghost
fn test_gtot (x:GR.ref int)
  requires GR.pts_to x 0
  ensures GR.pts_to x (f 0)
{
  open GR;
  let y = f 0;
  x := y
}
```

```pulse
fn increment (x:GR.ref int) (#n:erased int)
    requires GR.pts_to x n
    ensures GR.pts_to x (n + 1)
{  
   open GR;
   let v = !x;
   x := (v + 1);
}
```

```pulse
ghost
fn incrementg (x:GR.ref int) (#n:erased int)
    requires GR.pts_to x n
    ensures GR.pts_to x (n + 1)
{
   open GR;
   let v = !x;
   x := (v + 1)
}
```

```pulse
ghost
fn test_gtot_app_f (x:GR.ref int) (y:int)
  requires GR.pts_to x 0
  ensures GR.pts_to x y
{
  open GR;
  x := y
}
```

//
// ghost arguments to STGhost functions are ok
//
```pulse
ghost
fn test_gtot_app (x:GR.ref int)
  requires GR.pts_to x 0
  ensures GR.pts_to x (f 0)
{
  test_gtot_app_f x (f 0)
}
```
