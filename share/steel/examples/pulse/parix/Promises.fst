module Promises

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock

(* assuming a non-separating implication, we do not lose
the antecedent when eliminating. *)
assume val imp : vprop -> vprop -> vprop

let (@==>) = imp

assume
val intro_imp (p q : vprop)
  (extra : vprop)
  (f_elim : unit -> stt_ghost unit emp_inames (p ** extra) (fun () -> p ** q))
  : stt_ghost unit emp_inames
      extra
      (fun () -> p @==> q)

assume
val elim_imp (p q : vprop)
  : stt_ghost unit emp_inames
      (p ** (p @==> q))
      // maybe this should be:   p **  (p -->* p ** q)
      (fun () -> p ** q)

assume
val split_imp (p q r : vprop)
  (extra : vprop)
  : stt_ghost unit emp_inames
      (p @==> (q ** r))
      (fun () -> (p @==> q) ** (p @==> r))

let promise f v = f @==> v

let return_promise f v =
  intro_imp f v v
   (fun () -> return_stt_ghost_noeq () (fun _ -> f ** v))

let make_promise f v extra k =
  intro_imp f v extra k

friend Pulse.Lib.Steel
open Pulse.Lib.Steel

(* If v1 will hold in the future, and if we can in the future make a
promise that v2 will hold given v1, then we can promise v2 with the
same deadline. *)
let bind_promise #f #v1 #v2 extra k =
  magic()
 (* almost-proof... steel inference fails? *)
  // intro_imp f v2 (promise f v1 ** extra) (fun () ->
  //   mk_stt_ghost (fun () ->
  //     Steel.ST.Util.assert_ (f ** promise f v1 ** extra);
  //     elim_imp f v1 ();
  //     Steel.ST.Util.assert_ (f ** v1 ** extra);
  //     Steel.ST.Util.assert_ (f ** extra ** v1);
  //     reveal_stt_ghost (k ()) () <: Steel.ST.Effect.Ghost.STGhostT unit emp_inames (extra ** v1) (fun () -> promise f v2);
  //     Steel.ST.Util.assert_ (promise f v2 ** f);
  //     Steel.ST.Util.assert_ (f ** promise f v2);
  //     elim_imp f v2 ();
  //     Steel.ST.Util.assert_ (f ** v2);
  //     ()
  //   )
  // )

// Hmmmm.. does this make sense? Maybe this is just a task
// val promise_handle (f:vprop) (v:vprop) : Type0
// val wait_promise (#f:vprop) (#v:vprop)
//   (h : promise_handle f v)
//   : stt unit (promise f v) (fun _ -> 

(* We can define join_promise (NB: very brittle to write this in plain stt *)
let join_promise (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (promise f v1 ** promise f v2)
              (fun () -> promise f (v1 ** v2))
  = bind_promise (promise f v2) (fun () ->
    bind_promise v1 (fun () ->
    return_promise f (v1 ** v2)))

let split_promise (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (promise f (v1 ** v2))
              (fun () -> promise f v1 ** promise f v2)
  = split_imp _ _ _ emp

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

let redeem_promise f v =
  elim_imp f v
