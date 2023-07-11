open Prims
let rec zipWith :
  'a 'b 'c .
    ('a -> 'b -> ('c, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list ->
        'b Prims.list -> ('c Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun f ->
           fun l ->
             fun m ->
               match (l, m) with
               | ([], []) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
               | (x::xs, y::ys) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Match.fst"
                                    (Prims.of_int (16)) (Prims.of_int (20))
                                    (Prims.of_int (16)) (Prims.of_int (25)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Match.fst"
                                    (Prims.of_int (16)) (Prims.of_int (20))
                                    (Prims.of_int (16)) (Prims.of_int (44)))))
                           (Obj.magic (f x y))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Match.fst"
                                               (Prims.of_int (16))
                                               (Prims.of_int (29))
                                               (Prims.of_int (16))
                                               (Prims.of_int (44)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Match.fst"
                                               (Prims.of_int (16))
                                               (Prims.of_int (20))
                                               (Prims.of_int (16))
                                               (Prims.of_int (44)))))
                                      (Obj.magic (zipWith f xs ys))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 -> uu___ :: uu___1))))
                                uu___)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_V2_Derived.fail
                           "zipWith: length mismatch"))) uu___2 uu___1 uu___

type ('b1, 'b2) samepat = unit
type ('bs1, 'bs2) samepats = unit
let (open_st_term_bs :
  Pulse_Syntax_Base.st_term ->
    Pulse_Typing_Env.binding Prims.list ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun bs ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   let rec aux bs1 i =
                     match bs1 with
                     | [] -> []
                     | b::bs2 ->
                         (Pulse_Syntax_Naming.DT
                            (i,
                              (Pulse_Syntax_Pure.term_of_nvar
                                 (Pulse_Syntax_Base.ppname_default,
                                   (FStar_Pervasives_Native.fst b)))))
                         :: (aux bs2 (i + Prims.int_one)) in
                   let ss = aux (FStar_List_Tot_Base.rev bs) Prims.int_zero in
                   Pulse_Syntax_Naming.subst_st_term t ss))) uu___1 uu___
let (readback_binding :
  FStar_Reflection_V2_Data.binding ->
    (Pulse_Typing_Env.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun b ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match Pulse_Readback.readback_ty
                       b.FStar_Reflection_V2_Data.sort3
               with
               | FStar_Pervasives_Native.Some sort ->
                   ((b.FStar_Reflection_V2_Data.uniq1), sort)
               | FStar_Pervasives_Native.None ->
                   ((b.FStar_Reflection_V2_Data.uniq1),
                     {
                       Pulse_Syntax_Base.t =
                         (Pulse_Syntax_Base.Tm_FStar
                            (b.FStar_Reflection_V2_Data.sort3));
                       Pulse_Syntax_Base.range1 =
                         (FStar_Reflection_V2_Builtins.range_of_term
                            b.FStar_Reflection_V2_Data.sort3)
                     })))) uu___
let rec map_opt :
  'uuuuu 'uuuuu1 .
    ('uuuuu -> 'uuuuu1 FStar_Pervasives_Native.option) ->
      'uuuuu Prims.list -> 'uuuuu1 Prims.list FStar_Pervasives_Native.option
  =
  fun f ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives_Native.Some []
      | x::xs ->
          Pulse_Syntax_Pure.op_let_Question (f x)
            (fun y ->
               Pulse_Syntax_Pure.op_let_Question (map_opt f xs)
                 (fun ys -> FStar_Pervasives_Native.Some (y :: ys)))
let rec (r_bindings_to_string :
  FStar_Reflection_V2_Data.binding Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun bs ->
       match bs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | b::bs1 ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (74)) (Prims.of_int (4))
                            (Prims.of_int (74)) (Prims.of_int (90)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (74)) (Prims.of_int (4))
                            (Prims.of_int (74)) (Prims.of_int (116)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Match.fst"
                                  (Prims.of_int (74)) (Prims.of_int (5))
                                  (Prims.of_int (74)) (Prims.of_int (22)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Match.fst"
                                  (Prims.of_int (74)) (Prims.of_int (4))
                                  (Prims.of_int (74)) (Prims.of_int (90)))))
                         (Obj.magic
                            (FStar_Tactics_Unseal.unseal
                               b.FStar_Reflection_V2_Data.ppname3))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Match.fst"
                                             (Prims.of_int (74))
                                             (Prims.of_int (25))
                                             (Prims.of_int (74))
                                             (Prims.of_int (89)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Match.fst"
                                                   (Prims.of_int (74))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (74))
                                                   (Prims.of_int (89)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Match.fst"
                                                         (Prims.of_int (74))
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (74))
                                                         (Prims.of_int (89)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Match.fst"
                                                               (Prims.of_int (74))
                                                               (Prims.of_int (60))
                                                               (Prims.of_int (74))
                                                               (Prims.of_int (89)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "prims.fst"
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (31)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (83)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_V2_Builtins.term_to_string
                                                                  b.FStar_Reflection_V2_Data.sort3))
                                                            (fun uu___1 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___2
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___1
                                                                    " "))))
                                                      (fun uu___1 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___2 ->
                                                              Prims.strcat
                                                                ":" uu___1))))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat
                                                          (Prims.string_of_int
                                                             b.FStar_Reflection_V2_Data.uniq1)
                                                          uu___1))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat "-" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Match.fst"
                                       (Prims.of_int (74))
                                       (Prims.of_int (93))
                                       (Prims.of_int (74))
                                       (Prims.of_int (116)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "prims.fst"
                                       (Prims.of_int (590))
                                       (Prims.of_int (19))
                                       (Prims.of_int (590))
                                       (Prims.of_int (31)))))
                              (Obj.magic (r_bindings_to_string bs1))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> Prims.strcat uu___ uu___1))))
                        uu___)))) uu___
let rec (bindings_to_string :
  Pulse_Typing_Env.binding Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun bs ->
       match bs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | b::bs1 ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (80)) (Prims.of_int (4))
                            (Prims.of_int (80)) (Prims.of_int (85)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (80)) (Prims.of_int (4))
                            (Prims.of_int (80)) (Prims.of_int (109)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Match.fst"
                                  (Prims.of_int (80)) (Prims.of_int (29))
                                  (Prims.of_int (80)) (Prims.of_int (84)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (590)) (Prims.of_int (19))
                                  (Prims.of_int (590)) (Prims.of_int (31)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Match.fst"
                                        (Prims.of_int (80))
                                        (Prims.of_int (35))
                                        (Prims.of_int (80))
                                        (Prims.of_int (84)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "prims.fst"
                                        (Prims.of_int (590))
                                        (Prims.of_int (19))
                                        (Prims.of_int (590))
                                        (Prims.of_int (31)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Match.fst"
                                              (Prims.of_int (80))
                                              (Prims.of_int (35))
                                              (Prims.of_int (80))
                                              (Prims.of_int (78)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range "prims.fst"
                                              (Prims.of_int (590))
                                              (Prims.of_int (19))
                                              (Prims.of_int (590))
                                              (Prims.of_int (31)))))
                                     (Obj.magic
                                        (Pulse_Syntax_Printer.term_to_string
                                           (FStar_Pervasives_Native.snd b)))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             Prims.strcat uu___ " "))))
                               (fun uu___ ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 -> Prims.strcat ":" uu___))))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Prims.strcat
                                   (Prims.string_of_int
                                      (FStar_Pervasives_Native.fst b)) uu___))))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Match.fst"
                                       (Prims.of_int (80))
                                       (Prims.of_int (88))
                                       (Prims.of_int (80))
                                       (Prims.of_int (109)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "prims.fst"
                                       (Prims.of_int (590))
                                       (Prims.of_int (19))
                                       (Prims.of_int (590))
                                       (Prims.of_int (31)))))
                              (Obj.magic (bindings_to_string bs1))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> Prims.strcat uu___ uu___1))))
                        uu___)))) uu___
let (check_branch :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Checker_Common.check_t ->
            Pulse_Syntax_Base.pattern ->
              Pulse_Syntax_Base.st_term ->
                FStar_Reflection_V2_Data.binding Prims.list ->
                  ((Pulse_Syntax_Base.pattern, Pulse_Syntax_Base.st_term,
                     Pulse_Syntax_Base.comp_st,
                     (unit, unit, unit, unit) Pulse_Typing.br_typing)
                     FStar_Pervasives.dtuple4,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun check ->
            fun p0 ->
              fun e ->
                fun bs ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                             (Prims.of_int (96)) (Prims.of_int (2))
                             (Prims.of_int (96)) (Prims.of_int (58)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                             (Prims.of_int (96)) (Prims.of_int (59))
                             (Prims.of_int (112)) (Prims.of_int (22)))))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Match.fst"
                                   (Prims.of_int (96)) (Prims.of_int (10))
                                   (Prims.of_int (96)) (Prims.of_int (58)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Match.fst"
                                   (Prims.of_int (96)) (Prims.of_int (2))
                                   (Prims.of_int (96)) (Prims.of_int (58)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Match.fst"
                                         (Prims.of_int (96))
                                         (Prims.of_int (34))
                                         (Prims.of_int (96))
                                         (Prims.of_int (57)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "prims.fst"
                                         (Prims.of_int (590))
                                         (Prims.of_int (19))
                                         (Prims.of_int (590))
                                         (Prims.of_int (31)))))
                                (Obj.magic (r_bindings_to_string bs))
                                (fun uu___ ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        Prims.strcat "Extending 0 with: "
                                          uu___))))
                          (fun uu___ ->
                             (fun uu___ ->
                                Obj.magic
                                  (FStar_Tactics_V2_Builtins.print uu___))
                               uu___)))
                    (fun uu___ ->
                       (fun uu___ ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Match.fst"
                                        (Prims.of_int (97))
                                        (Prims.of_int (11))
                                        (Prims.of_int (97))
                                        (Prims.of_int (36)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Match.fst"
                                        (Prims.of_int (99))
                                        (Prims.of_int (2))
                                        (Prims.of_int (112))
                                        (Prims.of_int (22)))))
                               (Obj.magic
                                  (FStar_Tactics_Util.map readback_binding bs))
                               (fun uu___1 ->
                                  (fun bs1 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Match.fst"
                                                   (Prims.of_int (99))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (99))
                                                   (Prims.of_int (56)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Match.fst"
                                                   (Prims.of_int (99))
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (112))
                                                   (Prims.of_int (22)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Match.fst"
                                                         (Prims.of_int (99))
                                                         (Prims.of_int (10))
                                                         (Prims.of_int (99))
                                                         (Prims.of_int (56)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Match.fst"
                                                         (Prims.of_int (99))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (99))
                                                         (Prims.of_int (56)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Match.fst"
                                                               (Prims.of_int (99))
                                                               (Prims.of_int (34))
                                                               (Prims.of_int (99))
                                                               (Prims.of_int (55)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "prims.fst"
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (31)))))
                                                      (Obj.magic
                                                         (bindings_to_string
                                                            bs1))
                                                      (fun uu___1 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___2 ->
                                                              Prims.strcat
                                                                "Extending 1 with: "
                                                                uu___1))))
                                                (fun uu___1 ->
                                                   (fun uu___1 ->
                                                      Obj.magic
                                                        (FStar_Tactics_V2_Builtins.print
                                                           uu___1)) uu___1)))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Match.fst"
                                                              (Prims.of_int (100))
                                                              (Prims.of_int (11))
                                                              (Prims.of_int (100))
                                                              (Prims.of_int (29)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Match.fst"
                                                              (Prims.of_int (101))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (112))
                                                              (Prims.of_int (22)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Pulse_Typing.extend_env_bs
                                                             g bs1))
                                                     (fun uu___2 ->
                                                        (fun g' ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (71)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (22)))))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    e))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Before open : "
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___2))
                                                                    uu___2)))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    (open_st_term_bs
                                                                    e bs1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun e1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    e1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "After open : "
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___3))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    e1 pre ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e2, c,
                                                                    e_d) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (22)))))
                                                                    (if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e2.Pulse_Syntax_Base.range2))
                                                                    "Branch computation is not stateful"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (p0, e2,
                                                                    c,
                                                                    (Pulse_Typing.TBR
                                                                    (g, c,
                                                                    p0, e2,
                                                                    bs1, e_d)))))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                          uu___2))) uu___1)))
                                    uu___1))) uu___)
let (check_branches :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Checker_Common.check_t ->
            Pulse_Syntax_Base.branch Prims.list ->
              FStar_Reflection_V2_Data.binding Prims.list Prims.list ->
                ((Pulse_Syntax_Base.branch Prims.list,
                   Pulse_Syntax_Base.comp_st,
                   (unit, unit, unit) Pulse_Typing.brs_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun check ->
            fun brs0 ->
              fun bnds ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                           (Prims.of_int (126)) (Prims.of_int (2))
                           (Prims.of_int (126)) (Prims.of_int (50)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                           (Prims.of_int (126)) (Prims.of_int (51))
                           (Prims.of_int (154)) (Prims.of_int (18)))))
                  (if FStar_List_Tot_Base.isEmpty brs0
                   then
                     Obj.magic
                       (Obj.repr
                          (Pulse_Typing_Env.fail g
                             FStar_Pervasives_Native.None "empty match"))
                   else
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 -> ()))))
                  (fun uu___ ->
                     (fun uu___ ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Match.fst"
                                      (Prims.of_int (127))
                                      (Prims.of_int (23))
                                      (Prims.of_int (127))
                                      (Prims.of_int (27)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Match.fst"
                                      (Prims.of_int (126))
                                      (Prims.of_int (51))
                                      (Prims.of_int (154))
                                      (Prims.of_int (18)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> brs0))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   match uu___1 with
                                   | (p0, e0)::rest ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Match.fst"
                                                     (Prims.of_int (128))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (128))
                                                     (Prims.of_int (24)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Match.fst"
                                                     (Prims.of_int (127))
                                                     (Prims.of_int (30))
                                                     (Prims.of_int (154))
                                                     (Prims.of_int (18)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 -> bnds))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  match uu___2 with
                                                  | bnds0::bnds1 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (86)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (18)))))
                                                           (Obj.magic
                                                              (check_branch g
                                                                 pre ()
                                                                 post_hint
                                                                 check p0 e0
                                                                 bnds0))
                                                           (fun uu___3 ->
                                                              (fun uu___3 ->
                                                                 match uu___3
                                                                 with
                                                                 | FStar_Pervasives.Mkdtuple4
                                                                    (p01,
                                                                    e01, c0,
                                                                    d0) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun b ->
                                                                    fun bs ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    b))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (p, e) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    g pre ()
                                                                    post_hint
                                                                    check p e
                                                                    bs))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (p1, e1,
                                                                    c, d) ->
                                                                    Prims.Mkdtuple2
                                                                    ((p1, e1),
                                                                    d)))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun tr1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (zipWith
                                                                    tr1 rest
                                                                    bnds1))
                                                                    (fun r ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    r))))
                                                                    uu___4)))
                                                                    (fun
                                                                    brs_d ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((FStar_List_Tot_Base.map
                                                                    FStar_Pervasives.dfst
                                                                    brs_d),
                                                                    c0,
                                                                    (let rec aux
                                                                    brs =
                                                                    match brs
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Pulse_Typing.TBRS_0
                                                                    (g, c0)
                                                                    | 
                                                                    (Prims.Mkdtuple2
                                                                    ((p, e),
                                                                    d))::rest1
                                                                    ->
                                                                    Pulse_Typing.TBRS_1
                                                                    (g, c0,
                                                                    p, e, d,
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives.dfst
                                                                    rest1),
                                                                    (aux
                                                                    rest1)) in
                                                                    aux brs_d))))))
                                                                uu___3)))
                                                 uu___2))) uu___1))) uu___)
let (readback_pat_var :
  (FStar_Reflection_V2_Data.pattern * Prims.bool) ->
    (FStar_Reflection_Typing.pp_name_t * Prims.bool) Prims.list
      FStar_Pervasives_Native.option)
  =
  fun p ->
    match p with
    | (FStar_Reflection_V2_Data.Pat_Var (st, nm), i) ->
        FStar_Pervasives_Native.Some [(nm, i)]
    | (FStar_Reflection_V2_Data.Pat_Dot_Term uu___, uu___1) ->
        FStar_Pervasives_Native.Some []
    | uu___ -> FStar_Pervasives_Native.None
let op_let_Question :
  'uuuuu 'uuuuu1 .
    'uuuuu FStar_Pervasives_Native.option ->
      ('uuuuu -> 'uuuuu1 FStar_Pervasives_Native.option) ->
        'uuuuu1 FStar_Pervasives_Native.option
  =
  fun o ->
    fun f ->
      match o with
      | FStar_Pervasives_Native.Some x -> f x
      | uu___ -> FStar_Pervasives_Native.None
let (readback_pat :
  FStar_Reflection_V2_Data.pattern ->
    Pulse_Syntax_Base.pattern FStar_Pervasives_Native.option)
  =
  fun p ->
    match p with
    | FStar_Reflection_V2_Data.Pat_Cons (fv, uu___, args) ->
        let fv1 = FStar_Reflection_V2_Builtins.inspect_fv fv in
        op_let_Question (map_opt readback_pat_var args)
          (fun args1 ->
             let args2 = FStar_List_Tot_Base.flatten args1 in
             FStar_Pervasives_Native.Some
               (Pulse_Syntax_Base.Pat_Cons
                  ({
                     Pulse_Syntax_Base.fv_name = fv1;
                     Pulse_Syntax_Base.fv_range = FStar_Range.range_0
                   }, args2)))
    | FStar_Reflection_V2_Data.Pat_Constant c ->
        FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Pat_Constant c)
    | FStar_Reflection_V2_Data.Pat_Var (st, nm) ->
        FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Pat_Var nm)
    | uu___ -> FStar_Pervasives_Native.None
let (check_match :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.branch Prims.list ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Typing.post_hint_for_env ->
              Pulse_Checker_Common.check_t ->
                ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun sc ->
      fun brs ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun check ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                           (Prims.of_int (255)) (Prims.of_int (17))
                           (Prims.of_int (255)) (Prims.of_int (20)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                           (Prims.of_int (255)) (Prims.of_int (23))
                           (Prims.of_int (274)) (Prims.of_int (59)))))
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> brs))
                  (fun uu___ ->
                     (fun orig_brs ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Match.fst"
                                      (Prims.of_int (256))
                                      (Prims.of_int (35))
                                      (Prims.of_int (256))
                                      (Prims.of_int (50)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Match.fst"
                                      (Prims.of_int (255))
                                      (Prims.of_int (23))
                                      (Prims.of_int (274))
                                      (Prims.of_int (59)))))
                             (Obj.magic (Pulse_Checker_Pure.check_term g sc))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | FStar_Pervasives.Mkdtuple3
                                       (sc1, sc_ty, sc_typing) ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Match.fst"
                                                     (Prims.of_int (257))
                                                     (Prims.of_int (18))
                                                     (Prims.of_int (257))
                                                     (Prims.of_int (48)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Match.fst"
                                                     (Prims.of_int (257))
                                                     (Prims.of_int (51))
                                                     (Prims.of_int (274))
                                                     (Prims.of_int (59)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  FStar_List_Tot_Base.map
                                                    Pulse_Elaborate_Pure.elab_pat
                                                    (FStar_List_Tot_Base.map
                                                       FStar_Pervasives_Native.fst
                                                       brs)))
                                            (fun uu___1 ->
                                               (fun elab_pats ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Match.fst"
                                                                (Prims.of_int (260))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (263))
                                                                (Prims.of_int (72)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Match.fst"
                                                                (Prims.of_int (257))
                                                                (Prims.of_int (51))
                                                                (Prims.of_int (274))
                                                                (Prims.of_int (59)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (88)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (72)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_V2_Builtins.check_match_complete
                                                                   (Pulse_Typing.elab_env
                                                                    g)
                                                                   (Pulse_Elaborate_Pure.elab_term
                                                                    sc1)
                                                                   (Pulse_Elaborate_Pure.elab_term
                                                                    sc_ty)
                                                                   elab_pats))
                                                             (fun uu___1 ->
                                                                (fun uu___1
                                                                   ->
                                                                   match uu___1
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (sc1.Pulse_Syntax_Base.range1))
                                                                    "Could not check that match is correct"))
                                                                   | 
                                                                   FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (elab_pats1,
                                                                    bnds,
                                                                    tok)) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (elab_pats1,
                                                                    bnds,
                                                                    (Pulse_Typing.PC_Elab
                                                                    (g, sc1,
                                                                    sc_ty,
                                                                    elab_pats1,
                                                                    bnds,
                                                                    (FStar_Reflection_Typing.MC_Tok
                                                                    ((Pulse_Typing.elab_env
                                                                    g),
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    sc1),
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    sc_ty),
                                                                    elab_pats1,
                                                                    bnds,
                                                                    tok)))))))))
                                                                  uu___1)))
                                                       (fun uu___1 ->
                                                          (fun uu___1 ->
                                                             match uu___1
                                                             with
                                                             | FStar_Pervasives.Mkdtuple3
                                                                 (elab_pats',
                                                                  bnds',
                                                                  complete_d)
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    uu___1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    map_opt
                                                                    readback_pat
                                                                    elab_pats'))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    new_pats
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (59)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    new_pats
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (sc1.Pulse_Syntax_Base.range1))
                                                                    "failed to readback new patterns"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (zipWith
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun
                                                                    uu___4 ->
                                                                    (fun p ->
                                                                    fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (uu___6,
                                                                    e) ->
                                                                    (p, e))))
                                                                    uu___5
                                                                    uu___4)
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    new_pats)
                                                                    brs))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun brs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (check_branches
                                                                    g pre ()
                                                                    post_hint
                                                                    check
                                                                    brs1
                                                                    bnds'))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (brs2, c,
                                                                    brs_d) ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Match
                                                                    {
                                                                    Pulse_Syntax_Base.sc
                                                                    = sc1;
                                                                    Pulse_Syntax_Base.returns_
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.brs
                                                                    = brs2
                                                                    })), c,
                                                                    (Pulse_Typing.T_Match
                                                                    (g, sc1,
                                                                    sc_ty,
                                                                    (), c,
                                                                    brs2,
                                                                    brs_d,
                                                                    complete_d)))))))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                            uu___1))) uu___1)))
                                  uu___))) uu___)