module PulseExtractRust

open FStar.Compiler.Effect
open FStar.Compiler.Util

module R = RustBindings

let _ =
  print_string (R.add_2 R.one)