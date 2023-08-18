module Pulse.Lib.Steel

module S = Steel.Effect.Common
open Steel.ST.Effect
open Steel.ST.Effect.Atomic
open Steel.ST.Effect.Ghost
friend Pulse.Lib.Core
open Pulse.Lib.Core

val mk_stt
  (#a : Type)
  (#pre : S.vprop)
  (#post : a -> S.vprop)
  (f : unit -> STT a pre post)
  : stt a pre post
let mk_stt #a #pre #post f = f

val mk_stt_ghost
  (#a : Type)
  (#opened : inames)
  (#pre : S.vprop)
  (#post : a -> S.vprop)
  (f : unit -> STGhostT a opened pre post)
  : stt_ghost a opened pre post
let mk_stt_ghost f = f

val mk_stt_atomic
  (#a : Type)
  (#opened : inames)
  (#pre : S.vprop)
  (#post : a -> S.vprop)
  (f : unit -> STAtomicT a opened pre post)
  : stt_atomic a opened pre post
let mk_stt_atomic f = f

val reveal_stt
  (#a : Type)
  (#pre : S.vprop)
  (#post : a -> S.vprop)
  (f : stt a pre post)
  : (unit -> STT a pre post)
let reveal_stt #a #pre #post f = f

val reveal_stt_ghost
  (#a : Type)
  (#opened : inames)
  (#pre : S.vprop)
  (#post : a -> S.vprop)
  (f : stt_ghost a opened pre post)
  : (unit -> STGhostT a opened pre post)
let reveal_stt_ghost f = f

val reveal_stt_atomic
  (#a : Type)
  (#opened : inames)
  (#pre : S.vprop)
  (#post : a -> S.vprop)
  (f : stt_atomic a opened pre post)
  : unit -> STAtomicT a opened pre post
let reveal_stt_atomic f = f
