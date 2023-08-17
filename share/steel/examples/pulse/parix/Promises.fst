module Promises

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock

(* Assuming a magic-wand like operator on stt_ghost. Ideally we should
connect this to Tahina's magic stick, but I get a whole ton of errors
trying to do that. *)
assume val ( @==> ) : vprop -> vprop -> vprop
val intro_imp (p q : vprop)
  (extra : vprop)
  (f_elim : unit -> stt_ghost unit emp_inames (p ** extra) (fun () -> q))
  : stt_ghost unit emp_inames
      extra
      (fun () -> p @==> q)
let intro_imp p q extra f_elim = admit()

val elim_imp (p q : vprop)
  : stt_ghost unit emp_inames
      (p ** (p @==> q))
      // maybe this should be:   p **  (p -->* p ** q)
      (fun () -> q)
let elim_imp p q = admit()

(* A promise is just a magic stick that preserves the antecedent. *)
let promise f v = f @==> (f ** v)

let return_promise f v =
  intro_imp f (f ** v) v
   (fun () -> return_stt_ghost_noeq () (fun _ -> f ** v))

let make_promise f v extra k =
  intro_imp f (f ** v) extra k

let redeem_promise f v =
  elim_imp f (f ** v)

(* Pulse will currently not recognize calls to anything other than
top-level names, so this allows to force it. *)
val now
  (#a #inames #pre #post : _)
  (f : unit -> stt_ghost a inames pre post)
  : unit -> stt_ghost a inames pre post
let now f () = f ()

```pulse
ghost fn bind_promise_aux
  (f v1 v2 extra : vprop)
  (k : (unit -> stt_ghost unit emp_inames (f ** extra ** v1) (fun _ -> f ** promise f v2)))
  (_:unit)
  requires f  ** promise f v1 ** extra
  returns _:unit
  ensures f ** v2
{
  redeem_promise f v1;
  now k ();
  redeem_promise f v2
}
```

// FIXME: This should really work. Steel tactic getting in the way it seems?
(* If v1 will hold in the future, and if we can in the future make a
promise that v2 will hold given v1, then we can promise v2 with the
same deadline. *)
// ```pulse
// ghost fn __bind_promise
//   (#f #v1 #v2 : vprop) (extra : vprop)
//   (k : (unit -> stt_ghost unit emp_inames (f ** extra ** v1) (fun _ -> f ** promise f v2)))
//   requires promise f v1 ** extra
//   returns _:unit
//   ensures promise f v2
// {
//   let k = bind_promise_aux f v1 v2 extra k;
//   make_promise f v2 (extra ** promise f v1)
//       k
// }
// ```

let __bind_promise
  (#f #v1 #v2 : vprop) (extra : vprop)
  (k : (unit -> stt_ghost unit emp_inames (f ** extra ** v1) (fun _ -> f ** promise f v2)))
  : stt_ghost unit emp_inames (promise f v1 ** extra) (fun () -> promise f v2)
  =
  // make_promise f v2 (extra ** promise f v1)
  //   (bind_promise_aux f v1 v2 extra k)
  // Same
  admit()

let bind_promise #f #v1 #v2 extra k = admit()

(* let bind_promise #f #v1 #v2 extra k = *)
(*   intro_imp f (f ** v2) (promise f v1 ** extra) (fun () -> *)
(*     mk_stt_ghost (fun () -> *)
(*       Steel.ST.Util.assert_ (f ** promise f v1 ** extra); *)
(*       elim_imp f v1 (); *)
(*       Steel.ST.Util.assert_ (f ** v1 ** extra); *)
(*       Steel.ST.Util.assert_ (f ** extra ** v1); *)
(*       reveal_stt_ghost (k ()) () <: Steel.ST.Effect.Ghost.STGhostT unit emp_inames (extra ** v1) (fun () -> promise f v2); *)
(*       Steel.ST.Util.assert_ (promise f v2 ** f); *)
(*       Steel.ST.Util.assert_ (f ** promise f v2); *)
(*       elim_imp f v2 (); *)
(*       Steel.ST.Util.assert_ (f ** v2); *)
(*       () *)
(*     ) *)
(*   ) *)

(* We can define join_promise (NB: very brittle to write this in plain stt *)
let join_promise (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (promise f v1 ** promise f v2)
              (fun () -> promise f (v1 ** v2))
  = bind_promise (promise f v2) (fun () ->
    bind_promise v1 (fun () ->
    return_promise f (v1 ** v2)))

(* I'm not sure this is definable. Maybe it can be encoded
using invariants + a ghost ref stating whether the promise
was already split? *)
let split_promise (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (promise f (v1 ** v2))
              (fun () -> promise f v1 ** promise f v2)
  = admit() // split_imp _ _ _ emp

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
      bind_promise #_ #v1 #_ emp (fun () ->
        bind_sttg (rewrite (emp ** v1) v1 (vprop_equiv_unit v1)) (fun () ->
        bind_sttg (k ())
          (fun () -> return_promise f v2)))
    )
