module FlippableInv

open Pulse.Lib.Pervasives

val finv (p:vprop) : Type0

val off #p (fi : finv p) : vprop
val on  #p (fi : finv p) : vprop

val mk_finv (p:vprop) : stt (finv p) emp off

val flip_on  (#p:vprop) (fi : finv p) : stt unit (off fi ** p) (fun () -> on fi)
val flip_off (#p:vprop) (fi : finv p) : stt unit (on fi) (fun () -> off fi ** p)
