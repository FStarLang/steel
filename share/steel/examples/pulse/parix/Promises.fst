module Promises

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open Pulse.Lib.Stick

let comm_pre (#a:Type0) (#o:inames) (#pre1 #pre2 : vprop) (#post : a -> vprop)
  (f : stt_ghost a o (pre1 ** pre2) post)
     : stt_ghost a o (pre2 ** pre1) post
=
  sub_stt_ghost _ _ (vprop_equiv_comm _ _)
                    (intro_vprop_post_equiv _ _ (fun _ -> vprop_equiv_refl _))
                     f

let comm_post (#a:Type0) (#o:inames) (#pre : vprop) (#post1 #post2 : a -> vprop)
  (f : stt_ghost a o pre (fun x -> post1 x ** post2 x))
     : stt_ghost a o pre (fun x -> post2 x ** post1 x)
=
  sub_stt_ghost _ _ (vprop_equiv_refl _)
                    (intro_vprop_post_equiv _ _ (fun _ -> vprop_equiv_comm _ _))
                     f

(* A promise is just a magic stick that preserves the antecedent. *)
(* TODO: can this really be a ghost step? would we ever need to allocate invariants
to redeem? *)

let promise f v = f @==> (f ** v)

(* This should be definable once we fix the inames situation *)
assume
val ghost_sub_inv
  (#a:Type0) (#o1 #o2 : inames) (#pre : vprop) (#post : a -> vprop)
  (f : stt_ghost a o1 pre post)
  : Pure (stt_ghost a o2 pre post)
         (requires Set.subset o1 o2)
         (ensures fun _ -> True)

let return_promise f v =
  intro_stick f (f ** v) v
    (fun os ->
      let ff : stt_ghost unit emp_inames (f ** v) (fun _ -> f ** v) =
        return_stt_ghost_noeq () (fun _ -> f ** v)
      in
      let ff : stt_ghost unit os (f ** v) (fun _ -> f ** v) =
        ghost_sub_inv ff
      in
      let ff : stt_ghost unit os (v ** f) (fun _ -> f ** v) =
        comm_pre ff
      in
      ff)

let make_promise f v extra k =
  intro_stick f (f ** v) extra
    (fun os ->
      let kk : stt_ghost unit emp_inames (f ** extra) (fun _ -> f ** v) =
        k ()
      in
      let kk : stt_ghost unit os (f ** extra) (fun _ -> f ** v) =
        ghost_sub_inv kk
      in
      let kk : stt_ghost unit os (extra ** f) (fun _ -> f ** v) =
        comm_pre kk
      in
      kk)

let redeem_promise f v =
  comm_pre (elim_stick f (f ** v))

(* Pulse will currently not recognize calls to anything other than
top-level names, so this allows to force it. *)
val now
  (#a #inames #pre #post : _)
  (f : unit -> stt_ghost a inames pre post)
  : unit -> stt_ghost a inames pre post
let now f () = f ()

```pulse
ghost
fn bind_promise_aux
  (f v1 v2 extra : vprop)
  (k : (unit -> stt_ghost unit emp_inames (f ** extra ** v1) (fun _ -> f ** promise f v2)))
  (_:unit)
  requires f  ** (extra ** promise f v1)
  returns _:unit
  ensures f ** v2
{
  redeem_promise f v1;
  now k ();
  redeem_promise f v2
}
```

(* If v1 will hold in the future, and if we can in the future make a
promise that v2 will hold given v1, then we can promise v2 with the
same deadline. *)
```pulse
ghost
fn __bind_promise
  (#f #v1 #v2 : vprop) (extra : vprop)
  (k : (unit -> stt_ghost unit emp_inames (f ** extra ** v1) (fun _ -> f ** promise f v2)))
  requires promise f v1 ** extra
  returns _:unit
  ensures promise f v2
{
  let k
    : (unit -> stt_ghost unit emp_inames (f ** (extra ** promise f v1))
                                      (fun _ -> f ** v2))
    = bind_promise_aux f v1 v2 extra k;
  make_promise f v2 (extra ** promise f v1)
      k
}
```

let bind_promise #f #v1 #v2 extra k = __bind_promise #f #v1 #v2 extra k

inline_for_extraction
val frame_stt_ghost_left
  (#a:Type0)
  (#opens:inames)
  (#pre:vprop) (#post:a -> vprop)
  (frame:vprop)
  (e:stt_ghost a opens pre post)
  : stt_ghost a opens (frame ** pre) (fun x -> frame ** post x)
let frame_stt_ghost_left #a #opens #pre #post frame e =
  let e : stt_ghost a opens (pre ** frame) (fun x -> post x ** frame) =
    frame_stt_ghost frame e
  in
  let e : stt_ghost a opens (frame ** pre) (fun x -> post x ** frame) =
    comm_pre e
  in
  let e : stt_ghost a opens (frame ** pre) (fun x -> frame ** post x) =
    comm_post e
  in
  e

let bind_promise' #f #v1 #v2 extra k =
  let k : unit -> stt_ghost unit emp_inames (extra ** v1) (fun _ -> promise f v2) =
    k
  in
  let k : unit -> stt_ghost unit emp_inames (f ** (extra ** v1)) (fun _ -> f ** promise f v2) =
    fun () -> frame_stt_ghost_left f (k ())
  in
  let k : unit -> stt_ghost unit emp_inames (f ** extra ** v1) (fun _ -> f ** promise f v2) =
    fun () -> sub_stt_ghost _ _ 
                  (vprop_equiv_sym _ _ (vprop_equiv_assoc _ _ _))
                  (intro_vprop_post_equiv _ _ (fun _ -> vprop_equiv_refl _))
                  (k ())
  in
  bind_promise #f #v1 #v2 extra k

(* We can define join_promise (NB: very brittle to write this in plain stt *)
let join_promise (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (promise f v1 ** promise f v2)
              (fun () -> promise f (v1 ** v2))
  = bind_promise' (promise f v2) (fun () ->
    bind_promise' v1 (fun () ->
    return_promise f (v1 ** v2)))

(* split_promise *)
#set-options "--ext pulse:guard_policy=SMTSync"

module GR = Pulse.Lib.GhostReference

let inv_p' (f v1 v2 : vprop) (r1 r2 : GR.ref bool) (b1 b2 : bool) =
     GR.pts_to r1 #one_half b1
  ** GR.pts_to r2 #one_half b2
  ** (match b1, b2 with
      | false, false -> promise f (v1 ** v2)
      | false, true -> v1
      | true, false -> v2
      | true, true -> emp)

let inv_p (f v1 v2 : vprop) (r1 r2 : GR.ref bool) : vprop =
  exists_ (fun b1 -> exists_ (fun b2 -> inv_p' f v1 v2 r1 r2 b1 b2))

```pulse
ghost
fn __elim_l (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool) (i : inv (inv_p f v1 v2 r1 r2)) (_:unit)
  requires f ** GR.pts_to r1 #one_half false
  ensures f ** v1
{
  open Pulse.Lib.GhostReference;
  with_invariants i {
    unfold (inv_p f v1 v2 r1 r2);
    with bb1 bb2.
      assert (inv_p' f v1 v2 r1 r2 bb1 bb2);
    unfold (inv_p' f v1 v2 r1 r2 bb1 bb2);
    let b1 = !r1;
    let b2 = !r2;

    assert (pure (b1 == bb1));
    assert (pure (b2 == bb2));

    gather2 #_ #emp_inames
      r1
      #false #b1;

    let b1 : bool = stt_ghost_reveal _ b1;
    let b2 : bool = stt_ghost_reveal _ b2;

    if b2 {
      (* The "easy" case: the big promise has already been claimed
      by the other subpromise, so we just extract our resource. *)
      assert (pts_to r1 false);
      r1 := true;
      rewrite emp ** `@(match false, true with
                 | false, false -> promise f (v1 ** v2)
                 | false, true -> v1
                 | true, false -> v2
                 | true, true -> emp)
           as `@(match true, true with
                 | false, false -> promise f (v1 ** v2)
                 | false, true -> v1
                 | true, false -> v2
                 | true, true -> emp) ** v1;

      (* I don't understand why this remains in the ctx, but get rid
      of it as it's just emp *)
      rewrite `@(match true, true with
                 | false, false -> promise f (v1 ** v2)
                 | false, true -> v1
                 | true, false -> v2
                 | true, true -> emp)
           as emp;

      share2 #_ #emp_inames r1;
      fold (inv_p' f v1 v2 r1 r2 true true);
      fold (inv_p f v1 v2 r1 r2);
      assert (f ** v1 ** inv_p f v1 v2 r1 r2);
      drop_ (pts_to r1 #one_half true);
      ()
    } else {
      (* The "hard" case: the big promise has not been claimed.
      Claim it, split it, and store the leftover in the invariant. *)
      assert (pts_to r1 false);
      // assert (pts_to r2 false);

      rewrite `@(match false, false with
                 | false, false -> promise f (v1 ** v2)
                 | false, true -> v1
                 | true, false -> v2
                 | true, true -> emp)
           as promise f (v1 ** v2);

      redeem_promise f (v1 ** v2);

      assert (f ** v1 ** v2);

      r1 := true;

      rewrite v2
           as `@(match true, false with
                 | false, false -> promise f (v1 ** v2)
                 | false, true -> v1
                 | true, false -> v2
                 | true, true -> emp);

      share2 #_ #emp_inames r1;
      fold (inv_p' f v1 v2 r1 r2 true false);
      fold (inv_p f v1 v2 r1 r2);
      assert (f ** v1 ** inv_p f v1 v2 r1 r2);
      drop_ (pts_to r1 #one_half true);
      ()
    }
  }
}
```

```pulse
ghost
fn __elim_r (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool) (i : inv (inv_p f v1 v2 r1 r2)) (_:unit)
  requires f ** GR.pts_to r2 #one_half false
  ensures f ** v2
{
  (* Analogous to above... *)
  admit ()
}
```

(* Kinda bogus.. this is an unobservable step, not ghost *)
assume
val new_invariant_ghost #opened (p:vprop) : stt_ghost (inv p) opened p (fun _ -> emp)

#set-options "--print_implicits --print_universes"

```pulse
ghost
fn __split_promise (#f:vprop) (v1:vprop) (v2:vprop)
  requires promise f (v1 ** v2)
  ensures promise f v1 ** promise f v2
{
   let r1 = GR.alloc false;
   let r2 = GR.alloc false;
   GR.share2 #_ #emp_inames r1;
   GR.share2 #_ #emp_inames r2;

   rewrite (promise f (v1 ** v2))
        as `@(match false, false with
            | false, false -> promise f (v1 ** v2)
            | false, true -> v1
            | true, false -> v2
            | true, true -> emp);

  assert (
     GR.pts_to r1 #one_half false
  ** GR.pts_to r2 #one_half false
  ** `@(match false, false with
      | false, false -> promise f (v1 ** v2)
      | false, true -> v1
      | true, false -> v2
      | true, true -> emp));

  fold (inv_p' f v1 v2 r1 r2 false false);
  fold (inv_p f v1 v2 r1 r2);

  let i = new_invariant_ghost #emp_inames (inv_p f v1 v2 r1 r2);

  make_promise
    f
    v1
    (GR.pts_to r1 #one_half false)
    (__elim_l #f v1 v2 r1 r2 i);

  make_promise
    f
    v2
    (GR.pts_to r2 #one_half false)
    (__elim_r #f v1 v2 r1 r2 i);

  ()
}
```

let split_promise (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (promise f (v1 ** v2))
              (fun () -> promise f v1 ** promise f v2)
  = __split_promise #f v1 v2

(* /split_promise *)

let rewrite_promise (#f:vprop) (v1 : vprop) (v2 : vprop)
  (k : unit -> stt_ghost unit emp_inames v1 (fun _ -> v2))
  : stt_ghost unit
              emp_inames
              (promise f v1)
              (fun _ -> promise f v2)
= bind_sttg
    (rewrite (promise f v1) (promise f v1 ** emp)
       (vprop_equiv_trans _ _ _
         (vprop_equiv_sym _ _ (vprop_equiv_unit (promise f v1)))
         (vprop_equiv_comm _ _)))
    (fun () ->
      bind_promise' #_ #v1 #_ emp (fun () ->
        bind_sttg (rewrite (emp ** v1) v1 (vprop_equiv_unit v1)) (fun () ->
        bind_sttg (k ())
          (fun () -> return_promise f v2)))
    )
