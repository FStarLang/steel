module Pulse.Lib.DisposableInvariant

open Pulse.Lib.Pervasives

(* This is a Pulse wrapper over Steel.DisposableInvariant. It does not
yet have an implementation since we could not translate from the SteelAtomicUT into
stt_ghost, possibly since we just misunderstand the difference between Ghost and Unobservable.
We just add this interface for now in order to make progress on the Domains stuff. *)

/// The abstract type of ghost locks. Only used for proof purposes, will be erased at extraction time
val inv (p:vprop) : Type0

/// The name of a disposable invariant
val name (#p:_) (i:inv p) : Ghost.erased iname

/// Separation logic predicate stating that an invariant is currently active, and that we have permission [f]
/// on it. We can freely use the invariant as long as we have partial permission, but can only dispose of it
/// when we own the full permission.
/// The permission is annotated with the `smt_fallback` attribute, enabling automatic SMT rewritings on it
/// during frame inference
val active (#p:_) (f:perm) (_:inv p) : vprop

/// Creating a new invariant associated to vprop [p], as long as [p] was initially valid.
/// [p] is then removed from the context as it is now locked behind the invariant, and we
/// have full ownership on the newly minted invariant.
val new_inv (#opened:inames) (p:vprop)
  : stt_ghost (inv p) opened p
    (fun i -> active full_perm i)

/// Enables sharing an invariant between different threads.
val share (#p:vprop) (#f:perm) (#u:_) (i:inv p)
  : stt_ghost unit u
    (active f i)
    (fun _ -> active (half_perm f) i ** active (half_perm f) i)

/// Gathers an invariant that was previously shared.
val gather (#p:vprop) (#f0 #f1:perm) (#u:_) (i:inv p)
  : stt_ghost unit u
    (active f0 i ** active f1 i)
    (fun _ -> active (sum_perm f0 f1) i)

/// Some helpers to manipulate the set of currently opened invariants in the context.
let mem_inv (#p:vprop) (u:inames) (i:inv p) : GTot bool =
  Set.mem (reveal (name i)) (reveal u)

let add_inv (#p:vprop) (u:inames) (i:inv p) : inames =
  Set.union (Set.singleton (reveal (name i))) (reveal u)

/// If we have full ownership of the invariant, and it is not currently opened,
/// then we can dispose of it, and retrieve the locked resource
val dispose (#p:vprop) (#u:inames) (i:inv p{not (mem_inv u i)})
  : stt_ghost unit u
    (active full_perm i)
    (fun _ -> p)

/// Lifting the standard with_invariant combinator to disposable invariants.
/// If invariant [i], locking vprop [p] is not currently opened, then an atomic
/// computation [f] can access the locked resource [p] as long as it restores it
/// upon termination.
val with_invariant_ghost
   (#a:Type)
   (#fp:vprop)
   (#fp':a -> vprop)
   (#opened_invariants:inames)
   (#p:vprop)
   (#perm:_)
   (i:inv p{not (mem_inv opened_invariants i)})
   ($f:unit -> stt_ghost a (add_inv opened_invariants i)
                           (p ** fp)
                           (fun x -> p ** fp' x))
  : stt_ghost a opened_invariants
              (active perm i ** fp)
              (fun x -> active perm i ** fp' x)

val with_invariant_atomic
   (#a:Type)
   (#fp:vprop)
   (#fp':a -> vprop)
   (#opened_invariants:inames)
   (#p:vprop)
   (#perm:_)
   (i:inv p{not (mem_inv opened_invariants i)})
   ($f:unit -> stt_atomic a (add_inv opened_invariants i)
                            (p ** fp)
                            (fun x -> p ** fp' x))
  : stt_atomic a opened_invariants
               (active perm i ** fp)
               (fun x -> active perm i ** fp' x)
