open Prims
exception Splitlast_empty 
let (uu___is_Splitlast_empty : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Splitlast_empty -> true | uu___ -> false
let rec splitlast :
  'a .
    'a Prims.list ->
      (('a Prims.list * 'a), unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun l ->
       match l with
       | [] ->
           Obj.magic (Obj.repr (FStar_Tactics_Effect.raise Splitlast_empty))
       | x::[] ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ([], x))))
       | x::xs ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Recursion.fst"
                            (Prims.of_int (21)) (Prims.of_int (21))
                            (Prims.of_int (21)) (Prims.of_int (33)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Recursion.fst"
                            (Prims.of_int (20)) (Prims.of_int (12))
                            (Prims.of_int (22)) (Prims.of_int (17)))))
                   (Obj.magic (splitlast xs))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           match uu___ with
                           | (init, last) -> ((x :: init), last)))))) uu___
exception Map2_length_mismatch 
let (uu___is_Map2_length_mismatch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Map2_length_mismatch -> true | uu___ -> false
let rec map2 :
  'a 'b 'c .
    ('a -> 'b -> ('c, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list ->
        'b Prims.list -> ('c Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun f ->
           fun xs ->
             fun ys ->
               match (xs, ys) with
               | ([], []) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
               | (x::xx, y::yy) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Recursion.fst"
                                    (Prims.of_int (29)) (Prims.of_int (20))
                                    (Prims.of_int (29)) (Prims.of_int (25)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Recursion.fst"
                                    (Prims.of_int (29)) (Prims.of_int (20))
                                    (Prims.of_int (29)) (Prims.of_int (41)))))
                           (Obj.magic (f x y))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Recursion.fst"
                                               (Prims.of_int (29))
                                               (Prims.of_int (29))
                                               (Prims.of_int (29))
                                               (Prims.of_int (41)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Recursion.fst"
                                               (Prims.of_int (29))
                                               (Prims.of_int (20))
                                               (Prims.of_int (29))
                                               (Prims.of_int (41)))))
                                      (Obj.magic (map2 f xx yy))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 -> uu___ :: uu___1))))
                                uu___)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.raise Map2_length_mismatch)))
          uu___2 uu___1 uu___
let (debug_main :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun s ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "pulse.main"
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Recursion.fst"
                              (Prims.of_int (34)) (Prims.of_int (13))
                              (Prims.of_int (34)) (Prims.of_int (19)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Recursion.fst"
                              (Prims.of_int (34)) (Prims.of_int (7))
                              (Prims.of_int (34)) (Prims.of_int (19)))))
                     (Obj.magic (s ()))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___))
                          uu___)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let (string_as_term : Prims.string -> FStar_Reflection_Types.term) =
  fun s ->
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_Const
         (FStar_Reflection_V2_Data.C_String s))
let (add_knot :
  Pulse_Typing_Env.env ->
    FStar_Range.range ->
      Pulse_Syntax_Base.decl ->
        (Pulse_Syntax_Base.decl, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun rng ->
      fun d ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Recursion.fst"
                   (Prims.of_int (44)) (Prims.of_int (51))
                   (Prims.of_int (44)) (Prims.of_int (54)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Recursion.fst"
                   (Prims.of_int (43)) Prims.int_one (Prims.of_int (177))
                   (Prims.of_int (3)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> d.Pulse_Syntax_Base.d))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | Pulse_Syntax_Base.FnDefn
                    { Pulse_Syntax_Base.id = id;
                      Pulse_Syntax_Base.isrec = isrec;
                      Pulse_Syntax_Base.bs = bs;
                      Pulse_Syntax_Base.comp = comp;
                      Pulse_Syntax_Base.meas = meas;
                      Pulse_Syntax_Base.body7 = body;_}
                    ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Recursion.fst"
                                  (Prims.of_int (45)) (Prims.of_int (2))
                                  (Prims.of_int (46)) (Prims.of_int (62)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Recursion.fst"
                                  (Prims.of_int (46)) (Prims.of_int (63))
                                  (Prims.of_int (177)) (Prims.of_int (3)))))
                         (if Prims.uu___is_Nil bs
                          then
                            Obj.magic
                              (Obj.repr
                                 (Pulse_Typing_Env.fail g
                                    (FStar_Pervasives_Native.Some
                                       (d.Pulse_Syntax_Base.range3))
                                    "main: FnDefn does not have binders"))
                          else
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 -> ()))))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Recursion.fst"
                                             (Prims.of_int (48))
                                             (Prims.of_int (14))
                                             (Prims.of_int (48))
                                             (Prims.of_int (28)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Recursion.fst"
                                             (Prims.of_int (48))
                                             (Prims.of_int (31))
                                             (Prims.of_int (177))
                                             (Prims.of_int (3)))))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          Pulse_Elaborate_Pure.elab_comp comp))
                                    (fun uu___2 ->
                                       (fun r_res ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Recursion.fst"
                                                        (Prims.of_int (49))
                                                        (Prims.of_int (84))
                                                        (Prims.of_int (57))
                                                        (Prims.of_int (5)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Recursion.fst"
                                                        (Prims.of_int (59))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (177))
                                                        (Prims.of_int (3)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     fun qbv ->
                                                       match qbv with
                                                       | (q, b, bv) ->
                                                           {
                                                             FStar_Tactics_NamedView.uniq
                                                               =
                                                               (bv.Pulse_Syntax_Base.bv_index);
                                                             FStar_Tactics_NamedView.ppname
                                                               =
                                                               ((b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name);
                                                             FStar_Tactics_NamedView.sort
                                                               =
                                                               (Pulse_Elaborate_Pure.elab_term
                                                                  b.Pulse_Syntax_Base.binder_ty);
                                                             FStar_Tactics_NamedView.qual
                                                               =
                                                               (Pulse_Elaborate_Pure.elab_qual
                                                                  q);
                                                             FStar_Tactics_NamedView.attrs
                                                               = []
                                                           }))
                                               (fun uu___2 ->
                                                  (fun elab_b ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Recursion.fst"
                                                                   (Prims.of_int (59))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (61))
                                                                   (Prims.of_int (73)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Recursion.fst"
                                                                   (Prims.of_int (61))
                                                                   (Prims.of_int (74))
                                                                   (Prims.of_int (177))
                                                                   (Prims.of_int (3)))))
                                                          (Obj.magic
                                                             (debug_main g
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.string_of_list
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (uu___4,
                                                                    b,
                                                                    uu___5)
                                                                    ->
                                                                    Pulse_Syntax_Printer.binder_to_string
                                                                    b) bs))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "add_knot: bs = "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    "\n"))))))
                                                          (fun uu___2 ->
                                                             (fun uu___2 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (splitlast
                                                                    bs))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    b_knot)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.map
                                                                    elab_b
                                                                    bs1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    r_bs0 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun b ->
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    ((Prims.of_int (10000))
                                                                    +
                                                                    b.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (FStar_Sealed.map_seal
                                                                    b.FStar_Tactics_NamedView.ppname
                                                                    (fun s ->
                                                                    Prims.strcat
                                                                    s "'"));
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (b.FStar_Tactics_NamedView.sort);
                                                                    FStar_Tactics_NamedView.qual
                                                                    =
                                                                    (b.FStar_Tactics_NamedView.qual);
                                                                    FStar_Tactics_NamedView.attrs
                                                                    =
                                                                    (b.FStar_Tactics_NamedView.attrs)
                                                                    }))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    freshen_binder
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.map
                                                                    freshen_binder
                                                                    r_bs0))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun r_bs
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun b ->
                                                                    FStar_Reflection_V2_Builtins.pack_namedv
                                                                    {
                                                                    FStar_Reflection_V2_Data.uniq
                                                                    =
                                                                    (b.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Reflection_V2_Data.sort
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    b.FStar_Tactics_NamedView.sort);
                                                                    FStar_Reflection_V2_Data.ppname
                                                                    =
                                                                    (b.FStar_Tactics_NamedView.ppname)
                                                                    }))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    binder_to_r_namedv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (map2
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun
                                                                    uu___4 ->
                                                                    (fun b1
                                                                    ->
                                                                    fun b2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    ((binder_to_r_namedv
                                                                    b1),
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binder_to_term
                                                                    b2)))))
                                                                    uu___5
                                                                    uu___4)
                                                                    r_bs0
                                                                    r_bs))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    prime_subst
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (3)))))
                                                                    (if
                                                                    (Pulse_Syntax_Base.uu___is_C_STAtomic
                                                                    comp) ||
                                                                    (Pulse_Syntax_Base.uu___is_C_STGhost
                                                                    comp)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (19)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    meas
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (d.Pulse_Syntax_Base.range3))
                                                                    [
                                                                    Pulse_PP.text
                                                                    "'ghost' and 'atomic' recursive functions require a 'decreases' clause"]))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (splitlast
                                                                    r_bs))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (init,
                                                                    last) ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    init
                                                                    [
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Refine
                                                                    ({
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.sort);
                                                                    FStar_Tactics_NamedView.qual
                                                                    =
                                                                    FStar_Reflection_V2_Data.Q_Explicit;
                                                                    FStar_Tactics_NamedView.attrs
                                                                    = []
                                                                    },
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Range";
                                                                    "labeled"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Range";
                                                                    "range_0"]))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    "Could not prove termination"))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "precedes"]))),
                                                                    ((FStar_Reflection_V2_Builtins.subst_term
                                                                    prime_subst
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    meas))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((Pulse_Elaborate_Pure.elab_term
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    meas)),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))))));
                                                                    FStar_Tactics_NamedView.qual
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.qual);
                                                                    FStar_Tactics_NamedView.attrs
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.attrs)
                                                                    }]))))
                                                                    uu___4)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    r_bs))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    r_bs1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Reflection_V2_Builtins.subst_term
                                                                    prime_subst
                                                                    r_res))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    r_res1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    r_bs1
                                                                    r_res1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun r_ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (65)))))
                                                                    (if
                                                                    FStar_Reflection_V2_Data.uu___is_Tv_Unknown
                                                                    (FStar_Reflection_V2_Builtins.inspect_ln
                                                                    r_ty)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (d.Pulse_Syntax_Base.range3))
                                                                    "error: r_ty is Tv_unknown in add_knot?"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    Pulse_Syntax_Base.d
                                                                    =
                                                                    (Pulse_Syntax_Base.FnDefn
                                                                    {
                                                                    Pulse_Syntax_Base.id
                                                                    =
                                                                    (match 
                                                                    FStar_Reflection_V2_Builtins.inspect_ident
                                                                    id
                                                                    with
                                                                    | 
                                                                    (s, rng1)
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.pack_ident
                                                                    ((Prims.strcat
                                                                    "__recaux_"
                                                                    s), rng1));
                                                                    Pulse_Syntax_Base.isrec
                                                                    = false;
                                                                    Pulse_Syntax_Base.bs
                                                                    =
                                                                    (FStar_List_Tot_Base.op_At
                                                                    bs1
                                                                    [(
                                                                    match 
                                                                    FStar_Reflection_V2_Builtins.inspect_ident
                                                                    id
                                                                    with
                                                                    | 
                                                                    (s, rng1)
                                                                    ->
                                                                    (FStar_Pervasives_Native.None,
                                                                    (Pulse_Syntax_Base.mk_binder
                                                                    s rng1
                                                                    (Pulse_Syntax_Base.tm_fstar
                                                                    r_ty rng1)),
                                                                    {
                                                                    Pulse_Syntax_Base.bv_index
                                                                    =
                                                                    ((FStar_Pervasives_Native.__proj__Mktuple3__item___3
                                                                    b_knot).Pulse_Syntax_Base.bv_index);
                                                                    Pulse_Syntax_Base.bv_ppname
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.name
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    s);
                                                                    Pulse_Syntax_Base.range
                                                                    = rng1
                                                                    }
                                                                    }))]);
                                                                    Pulse_Syntax_Base.comp
                                                                    = comp;
                                                                    Pulse_Syntax_Base.meas
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.body7
                                                                    = body
                                                                    });
                                                                    Pulse_Syntax_Base.range3
                                                                    =
                                                                    (d.Pulse_Syntax_Base.range3)
                                                                    }))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                               uu___2)))
                                                    uu___2))) uu___2)))
                              uu___1))) uu___)
let (tie_knot :
  Pulse_Typing_Env.env ->
    FStar_Range.range ->
      Prims.string ->
        Prims.string ->
          Pulse_Syntax_Base.decl ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Typing.blob ->
                (unit FStar_Reflection_Typing.sigelt_for Prims.list, 
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun rng ->
      fun nm_orig ->
        fun nm_aux ->
          fun d ->
            fun r_typ ->
              fun blob ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Recursion.fst"
                           (Prims.of_int (184)) (Prims.of_int (18))
                           (Prims.of_int (191)) (Prims.of_int (15)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Recursion.fst"
                           (Prims.of_int (192)) (Prims.of_int (4))
                           (Prims.of_int (198)) (Prims.of_int (22)))))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Recursion.fst"
                                 (Prims.of_int (187)) (Prims.of_int (16))
                                 (Prims.of_int (187)) (Prims.of_int (36)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Recursion.fst"
                                 (Prims.of_int (184)) (Prims.of_int (18))
                                 (Prims.of_int (191)) (Prims.of_int (15)))))
                        (Obj.magic
                           (FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                              r_typ))
                        (fun uu___ ->
                           (fun uu___ ->
                              match uu___ with
                              | (bs, c) ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Recursion.fst"
                                                (Prims.of_int (188))
                                                (Prims.of_int (4))
                                                (Prims.of_int (188))
                                                (Prims.of_int (64)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Recursion.fst"
                                                (Prims.of_int (188))
                                                (Prims.of_int (65))
                                                (Prims.of_int (191))
                                                (Prims.of_int (15)))))
                                       (if Prims.uu___is_Nil bs
                                        then
                                          Obj.magic
                                            (Obj.repr
                                               (Pulse_Typing_Env.fail g
                                                  (FStar_Pervasives_Native.Some
                                                     rng)
                                                  "tie_knot: impossible (1)"))
                                        else
                                          Obj.magic
                                            (Obj.repr
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 -> ()))))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Recursion.fst"
                                                           (Prims.of_int (189))
                                                           (Prims.of_int (13))
                                                           (Prims.of_int (189))
                                                           (Prims.of_int (20)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Recursion.fst"
                                                           (Prims.of_int (190))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (191))
                                                           (Prims.of_int (15)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        FStar_List_Tot_Base.init
                                                          bs))
                                                  (fun uu___2 ->
                                                     (fun bs1 ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (64)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (15)))))
                                                             (if
                                                                Prims.uu___is_Nil
                                                                  bs1
                                                              then
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    rng)
                                                                    "tie_knot: impossible (2)"))
                                                              else
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                             (fun uu___2 ->
                                                                (fun uu___2
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.mk_arr
                                                                    bs1 c))
                                                                  uu___2)))
                                                       uu___2))) uu___1)))
                             uu___)))
                  (fun uu___ ->
                     (fun knot_r_typ ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Recursion.fst"
                                      (Prims.of_int (195))
                                      (Prims.of_int (21))
                                      (Prims.of_int (195))
                                      (Prims.of_int (86)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Recursion.fst"
                                      (Prims.of_int (192)) (Prims.of_int (4))
                                      (Prims.of_int (198))
                                      (Prims.of_int (22)))))
                             (Obj.magic
                                (FStar_Reflection_Typing.mk_unchecked_let
                                   (Pulse_Typing_Env.fstar_env g) nm_orig
                                   (FStar_Reflection_V2_Builtins.pack_ln
                                      (FStar_Reflection_V2_Data.Tv_App
                                         ((FStar_Reflection_V2_Builtins.pack_ln
                                             (FStar_Reflection_V2_Data.Tv_FVar
                                                (FStar_Reflection_V2_Builtins.pack_fv
                                                   ["Prims"; "magic"]))),
                                           ((FStar_Reflection_V2_Builtins.pack_ln
                                               (FStar_Reflection_V2_Data.Tv_Const
                                                  FStar_Reflection_V2_Data.C_Unit)),
                                             FStar_Reflection_V2_Data.Q_Explicit))))
                                   knot_r_typ))
                             (fun uu___ ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     match uu___ with
                                     | (flag, sig1, uu___2) ->
                                         [(flag,
                                            (Pulse_RuntimeUtils.add_attribute
                                               sig1
                                               (FStar_Reflection_V2_Builtins.pack_ln
                                                  (FStar_Reflection_V2_Data.Tv_App
                                                     ((FStar_Reflection_V2_Builtins.pack_ln
                                                         (FStar_Reflection_V2_Data.Tv_App
                                                            ((FStar_Reflection_V2_Builtins.pack_ln
                                                                (FStar_Reflection_V2_Data.Tv_FVar
                                                                   (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"]))),
                                                              ((FStar_Reflection_V2_Builtins.pack_ln
                                                                  (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    "pulse.recursive.knot"))),
                                                                FStar_Reflection_V2_Data.Q_Explicit)))),
                                                       ((string_as_term
                                                           nm_aux),
                                                         FStar_Reflection_V2_Data.Q_Explicit))))),
                                            (FStar_Pervasives_Native.Some
                                               blob))])))) uu___)