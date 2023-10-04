type i64 = Int64.t

let one = Int64.one

module Rust = struct
  external add_2 : i64 -> string = "rust_add_2"

end
let add_2 (x:i64) = Rust.add_2 x
