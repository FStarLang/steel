module Async

open Pulse.Lib.Pervasives
open Promises
open UnixFork

let ref_solves_post (#a:Type0) (r:ref (option a)) (post : a -> vprop) : vprop =
  exists_ (fun (v:a) -> pts_to r (Some v) ** post v)

(* NB: The vprop is not used here, so why the index? Only to make
it easier for users to call await, as the post should be unified
and hence the user would not need to explicitly repeat it. Unless
we can fill it from the context...? *)
let asynch (a:Type0) (post : a -> vprop) : Type0 =
  ref (option a) & thread

let async_joinable #a post h =
  joinable (snd h) ** promise (done (snd h)) (ref_solves_post (fst h) post)

// val async
//   (#a : Type0)
//   (#pre : vprop)
//   (#post : a -> vprop)
//   (f : unit -> stt a pre post)
//   : stt (asynch a post) pre (fun h -> async_joinable h)
// let async #a #pre #post f =
//   bind_stt (alloc None) (fun h ->
//   let th = fork (fun () -> bind_stt (f ()) (fun (x:a) -> h := Some a)) in
//   (| h, th |))

```pulse
fn async_fill
  (#a : Type0)
  (#pre : vprop)
  (#post : (a -> vprop))
  (f : (unit -> stt a pre (fun x -> post x)))
  (r : ref (option a))
  (_:unit)
  requires pre ** pts_to r None
  returns _ : unit
  ensures ref_solves_post r post
{
// This should really just work
//   assert pre;
//   let v : a = f ();
//   assert (post v);
//   r := Some v;
//   ()
  admit()
}
```

```pulse
fn __async
  (#a : Type0)
  (#pre : vprop)
  (#post : (a -> vprop))
  (f : (unit -> stt a pre post))
  requires pre
  returns h : asynch a post
  ensures async_joinable post h
{
  let r = alloc (None #a);
//   let th = fork #(pre ** pts_to r None) #(exists_ (fun (v:a) -> pts_to r (Some v) ** post v))
//              (fun () -> async_fill #a #pre #post f r ());

  // let k
  //   : (unit -> stt u#0 unit (pre ** pts_to u#0 #(option u#0 a) r #full_perm (None u#0 #a))
  //                           (fun () -> ref_solves_post #a r post))
  //   = (fun () -> async_fill #a #pre #post f r ());
  let th = fork #(pre ** pts_to r None) #(ref_solves_post r post)
                (fun () -> magic()); // FIXME... it's the thing above
  let res = ( r, th );
  
  assert (joinable th);
  assert (promise (done th) (ref_solves_post r post));
  rewrite (joinable th ** promise (done th) (ref_solves_post r post))
       as (async_joinable post res);
  res
}
```
let async = __async

```pulse
fn __await
  (#a : Type0)
  (#post : (a -> vprop))
  (h : asynch a post)
  requires async_joinable post h
  returns x:a
  ensures post x
{
  let r = fst h;
  let th = snd h;
  unfold async_joinable post h;
  assert (joinable th);
  join th;
  assert (done th);
  rewrite (done th) as (done (snd h));
  redeem_promise (done (snd h)) (ref_solves_post r post);
  assert (ref_solves_post r post);
  unfold ref_solves_post r post;
  with vv. assert (pts_to r (Some vv));
  drop_ (done th);
  
  assert (post vv);
  assert (pts_to r (Some vv));

  let vo = !r;
  free r;
  match vo {
    Some v -> {
      rewrite (post vv) as (post v);
      assert (post v);
      v
    }
  }
}
```
let await = __await
