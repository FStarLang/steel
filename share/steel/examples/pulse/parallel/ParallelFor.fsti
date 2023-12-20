module ParallelFor

open Pulse.Lib.Pervasives

let rec range (p : nat -> vprop) (i j : nat) : Tot vprop (decreases j-i) =
  if i < j
  then p i ** range p (i+1) j
  else emp

```pulse
val
fn
parallel_for
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> (post i))))
  (n : pos)
  requires range pre 0 n
  ensures range post 0 n
```

(* Alternative; not splitting the pool_alive resource. We are anyway
spawning sequentially. *)
```pulse
val
fn
parallel_for_alt
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> (post i))))
  (n : pos)
  requires range pre 0 n
  ensures range post 0 n
```

```pulse
val
fn
parallel_for_wsr
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (full_pre : (nat -> vprop))
  (full_post : (nat -> vprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> post i)))
  (unfold_pre : (i:nat -> stt_ghost unit emp_inames (full_pre (i+1)) (fun () -> pre i ** full_pre i)))
  (fold_post : (i:nat -> stt_ghost unit emp_inames (post i ** full_post i) (fun () -> full_post (i+1))))
  (n : pos)
  requires full_pre n ** full_post 0
  ensures full_pre 0 ** full_post n
```

```pulse
val
fn
parallel_for_hier
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> (post i))))
  (n : pos)
  requires range pre 0 n
  ensures range post 0 n
```