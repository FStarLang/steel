open Prims
type 'fits fits_t = Prims.int
type 't bounded_int =
  {
  fits: unit ;
  v: unit ;
  u: unit ;
  op_Plus: 't -> 't -> 't ;
  op_Subtraction: 't -> 't -> 't ;
  op_Less: 't -> 't -> Prims.bool ;
  op_Less_Equals: 't -> 't -> Prims.bool ;
  op_Percent: 't -> 't -> 't ;
  properties: unit }
let __proj__Mkbounded_int__item__op_Plus :
  't . 't bounded_int -> 't -> 't -> 't =
  fun projectee ->
    match projectee with
    | { fits; v; u; op_Plus; op_Subtraction; op_Less; op_Less_Equals;
        op_Percent; properties;_} -> op_Plus
let __proj__Mkbounded_int__item__op_Subtraction :
  't . 't bounded_int -> 't -> 't -> 't =
  fun projectee ->
    match projectee with
    | { fits; v; u; op_Plus; op_Subtraction; op_Less; op_Less_Equals;
        op_Percent; properties;_} -> op_Subtraction
let __proj__Mkbounded_int__item__op_Less :
  't . 't bounded_int -> 't -> 't -> Prims.bool =
  fun projectee ->
    match projectee with
    | { fits; v; u; op_Plus; op_Subtraction; op_Less; op_Less_Equals;
        op_Percent; properties;_} -> op_Less
let __proj__Mkbounded_int__item__op_Less_Equals :
  't . 't bounded_int -> 't -> 't -> Prims.bool =
  fun projectee ->
    match projectee with
    | { fits; v; u; op_Plus; op_Subtraction; op_Less; op_Less_Equals;
        op_Percent; properties;_} -> op_Less_Equals
let __proj__Mkbounded_int__item__op_Percent :
  't . 't bounded_int -> 't -> 't -> 't =
  fun projectee ->
    match projectee with
    | { fits; v; u; op_Plus; op_Subtraction; op_Less; op_Less_Equals;
        op_Percent; properties;_} -> op_Percent
type ('t, 'projectee, 'uuuuu) fits = Obj.t
let op_Plus : 't . 't bounded_int -> 't -> 't -> 't =
  fun projectee ->
    match projectee with
    | { fits = fits1; v; u; op_Plus = op_Plus1; op_Subtraction; op_Less;
        op_Less_Equals; op_Percent; properties;_} -> op_Plus1
let op_Subtraction : 't . 't bounded_int -> 't -> 't -> 't =
  fun projectee ->
    match projectee with
    | { fits = fits1; v; u; op_Plus = op_Plus1;
        op_Subtraction = op_Subtraction1; op_Less; op_Less_Equals;
        op_Percent; properties;_} -> op_Subtraction1
let op_Less : 't . 't bounded_int -> 't -> 't -> Prims.bool =
  fun projectee ->
    match projectee with
    | { fits = fits1; v; u; op_Plus = op_Plus1;
        op_Subtraction = op_Subtraction1; op_Less = op_Less1; op_Less_Equals;
        op_Percent; properties;_} -> op_Less1
let op_Less_Equals : 't . 't bounded_int -> 't -> 't -> Prims.bool =
  fun projectee ->
    match projectee with
    | { fits = fits1; v; u; op_Plus = op_Plus1;
        op_Subtraction = op_Subtraction1; op_Less = op_Less1;
        op_Less_Equals = op_Less_Equals1; op_Percent; properties;_} ->
        op_Less_Equals1
let op_Percent : 't . 't bounded_int -> 't -> 't -> 't =
  fun projectee ->
    match projectee with
    | { fits = fits1; v; u; op_Plus = op_Plus1;
        op_Subtraction = op_Subtraction1; op_Less = op_Less1;
        op_Less_Equals = op_Less_Equals1; op_Percent = op_Percent1;
        properties;_} -> op_Percent1
let (bounded_int_int : Prims.int bounded_int) =
  {
    fits = ();
    v = ();
    u = ();
    op_Plus = (fun x -> fun y -> x + y);
    op_Subtraction = (fun x -> fun y -> x - y);
    op_Less = (fun x -> fun y -> x < y);
    op_Less_Equals = (fun x -> fun y -> x <= y);
    op_Percent = (fun x -> fun y -> x mod y);
    properties = ()
  }
type 't bounded_unsigned =
  {
  base: 't bounded_int ;
  max_bound: 't ;
  static_max_bound: Prims.bool ;
  properties1: unit }
let __proj__Mkbounded_unsigned__item__base :
  't . 't bounded_unsigned -> 't bounded_int =
  fun projectee ->
    match projectee with
    | { base; max_bound; static_max_bound; properties1 = properties;_} ->
        base
let __proj__Mkbounded_unsigned__item__max_bound :
  't . 't bounded_unsigned -> 't =
  fun projectee ->
    match projectee with
    | { base; max_bound; static_max_bound; properties1 = properties;_} ->
        max_bound
let __proj__Mkbounded_unsigned__item__static_max_bound :
  't . 't bounded_unsigned -> Prims.bool =
  fun projectee ->
    match projectee with
    | { base; max_bound; static_max_bound; properties1 = properties;_} ->
        static_max_bound
let max_bound : 't . 't bounded_unsigned -> 't =
  fun projectee ->
    match projectee with
    | { base; max_bound = max_bound1; static_max_bound;
        properties1 = properties;_} -> max_bound1
let bounded_from_bounded_unsigned :
  't . 't bounded_unsigned -> 't bounded_int = fun c -> c.base
let safe_add :
  't . 't bounded_unsigned -> 't -> 't -> 't FStar_Pervasives_Native.option =
  fun c ->
    fun x ->
      fun y ->
        if c.static_max_bound
        then
          (if
             op_Less_Equals (bounded_from_bounded_unsigned c) y
               (op_Subtraction (bounded_from_bounded_unsigned c)
                  (max_bound c) x)
           then
             FStar_Pervasives_Native.Some
               (op_Plus (bounded_from_bounded_unsigned c) x y)
           else FStar_Pervasives_Native.None)
        else
          if op_Less_Equals (bounded_from_bounded_unsigned c) x (max_bound c)
          then
            (if
               op_Less_Equals (bounded_from_bounded_unsigned c) y
                 (op_Subtraction (bounded_from_bounded_unsigned c)
                    (max_bound c) x)
             then
               FStar_Pervasives_Native.Some
                 (op_Plus (bounded_from_bounded_unsigned c) x y)
             else FStar_Pervasives_Native.None)
          else FStar_Pervasives_Native.None
type ('t, 'c, 'op, 'x, 'y) ok = Obj.t
let add : 't . 't bounded_int -> 't -> 't -> 't =
  fun uu___ -> fun x -> fun y -> op_Plus uu___ x y
let add3 : 't . 't bounded_int -> 't -> 't -> 't -> 't =
  fun uu___ -> fun x -> fun y -> fun z -> op_Plus uu___ (op_Plus uu___ x y) z
let add3_alt : 't . 't bounded_int -> 't -> 't -> 't -> 't =
  fun uu___ -> fun x -> fun y -> fun z -> op_Plus uu___ (op_Plus uu___ x y) z
let (bounded_int_u32 : FStar_UInt32.t bounded_int) =
  {
    fits = ();
    v = ();
    u = ();
    op_Plus = (fun x -> fun y -> FStar_UInt32.add x y);
    op_Subtraction = (fun x -> fun y -> FStar_UInt32.sub x y);
    op_Less = (fun x -> fun y -> FStar_UInt32.lt x y);
    op_Less_Equals = (fun x -> fun y -> FStar_UInt32.lte x y);
    op_Percent = (fun x -> fun y -> FStar_UInt32.rem x y);
    properties = ()
  }
let (bounded_unsigned_u32 : FStar_UInt32.t bounded_unsigned) =
  {
    base = bounded_int_u32;
    max_bound = (Stdint.Uint32.of_string "0xffffffff");
    static_max_bound = true;
    properties1 = ()
  }
let (bounded_int_u64 : FStar_UInt64.t bounded_int) =
  {
    fits = ();
    v = ();
    u = ();
    op_Plus = (fun x -> fun y -> FStar_UInt64.add x y);
    op_Subtraction = (fun x -> fun y -> FStar_UInt64.sub x y);
    op_Less = (fun x -> fun y -> FStar_UInt64.lt x y);
    op_Less_Equals = (fun x -> fun y -> FStar_UInt64.lte x y);
    op_Percent = (fun x -> fun y -> FStar_UInt64.rem x y);
    properties = ()
  }
let (bounded_unsigned_u64 : FStar_UInt64.t bounded_unsigned) =
  {
    base = bounded_int_u64;
    max_bound = (Stdint.Uint64.of_string "0xffffffffffffffff");
    static_max_bound = true;
    properties1 = ()
  }
let (add_u32 : FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun x -> fun y -> op_Plus bounded_int_u32 x y
let (sub_u32 : FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun x -> fun y -> op_Subtraction bounded_int_u32 x y
let (add_nat_1 : Prims.nat -> Prims.int) =
  fun x -> op_Plus bounded_int_int x Prims.int_one
let (nat_as_int : Prims.nat -> Prims.int) = fun x -> x
let (bounded_int_nat : Prims.nat bounded_int) =
  {
    fits = ();
    v = ();
    u = ();
    op_Plus = (fun x -> fun y -> x + y);
    op_Subtraction = (fun x -> fun y -> x - y);
    op_Less = (fun x -> fun y -> x < y);
    op_Less_Equals = (fun x -> fun y -> x <= y);
    op_Percent = (fun x -> fun y -> x mod y);
    properties = ()
  }
let (add_nat : Prims.nat -> Prims.nat -> Prims.nat) =
  fun x -> fun y -> op_Plus bounded_int_nat x y
let (bounded_int_size_t : FStar_SizeT.t bounded_int) =
  {
    fits = ();
    v = ();
    u = ();
    op_Plus = (fun x -> fun y -> FStar_SizeT.add x y);
    op_Subtraction = (fun x -> fun y -> FStar_SizeT.sub x y);
    op_Less = (fun x -> fun y -> FStar_SizeT.lt x y);
    op_Less_Equals = (fun x -> fun y -> FStar_SizeT.lte x y);
    op_Percent = (fun x -> fun y -> FStar_SizeT.rem x y);
    properties = ()
  }
let (size_t_plus_one : FStar_SizeT.t -> FStar_SizeT.t) =
  fun x -> op_Plus bounded_int_size_t x Stdint.Uint64.one