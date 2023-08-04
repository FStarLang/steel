module Bug.ImpossibleMatch
open Pulse.Lib.Pervasives

```pulse
fn test (x: ref int)
    requires pts_to x full_perm 0
    returns b:bool
    ensures `@(if b then pts_to x full_perm 0 else pts_to x full_perm 1)
{
    true;
}
```

val test1 (x: ref int)
 : stt bool (pts_to x full_perm 0)
            (fun b -> if b then pts_to x full_perm 0 else pts_to x full_perm 1)

let test1 = test

val test2 (x: ref int)
 : stt bool (pts_to x full_perm 0)
            (fun b -> match b with | true -> pts_to x full_perm 0 | _ -> pts_to x full_perm 1)
let test2 = test

val test3 (x: ref int)
 : stt bool (pts_to x full_perm 0)
            (fun b -> match b with | true -> pts_to x full_perm 0 | false -> pts_to x full_perm 1)

(*
//crashes with an Impossible! (Tm_match)
let test3 = test
*)