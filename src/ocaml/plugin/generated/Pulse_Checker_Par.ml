open Prims
let (vprop_equiv_equiv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop FStar_Algebra_CommMonoid_Equiv.equiv)
  = fun g -> FStar_Algebra_CommMonoid_Equiv.EQ ((), (), (), ())
let (vprop_monoid :
  Pulse_Typing_Env.env ->
    (Pulse_Syntax_Base.vprop, unit) FStar_Algebra_CommMonoid_Equiv.cm)
  =
  fun g ->
    FStar_Algebra_CommMonoid_Equiv.CM
      (Pulse_Syntax_Base.tm_emp, Pulse_Syntax_Base.tm_star, (), (), (), ())
let (print_term :
  Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Par.fst"
               (Prims.of_int (101)) (Prims.of_int (12)) (Prims.of_int (101))
               (Prims.of_int (30)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Par.fst"
               (Prims.of_int (101)) (Prims.of_int (4)) (Prims.of_int (101))
               (Prims.of_int (30)))))
      (Obj.magic (Pulse_Syntax_Printer.term_to_string t))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (FStar_Tactics_V2_Builtins.print uu___))
           uu___)
let rec (print_list_terms' :
  Pulse_Syntax_Base.term Prims.list ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun l ->
    match l with
    | [] -> FStar_Tactics_V2_Builtins.print "]"
    | t::q ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                   (Prims.of_int (106)) (Prims.of_int (11))
                   (Prims.of_int (106)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                   (Prims.of_int (106)) (Prims.of_int (25))
                   (Prims.of_int (106)) (Prims.of_int (58)))))
          (Obj.magic (FStar_Tactics_V2_Builtins.print ", "))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (106)) (Prims.of_int (25))
                              (Prims.of_int (106)) (Prims.of_int (37)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (106)) (Prims.of_int (39))
                              (Prims.of_int (106)) (Prims.of_int (58)))))
                     (Obj.magic (print_term t))
                     (fun uu___1 ->
                        (fun uu___1 -> Obj.magic (print_list_terms' q))
                          uu___1))) uu___)
let (print_list_terms :
  Pulse_Syntax_Base.term Prims.list ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun l ->
    match l with
    | [] -> FStar_Tactics_V2_Builtins.print "[]"
    | t::q ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                   (Prims.of_int (111)) (Prims.of_int (13))
                   (Prims.of_int (111)) (Prims.of_int (24)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                   (Prims.of_int (111)) (Prims.of_int (26))
                   (Prims.of_int (111)) (Prims.of_int (59)))))
          (Obj.magic (FStar_Tactics_V2_Builtins.print "["))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (111)) (Prims.of_int (26))
                              (Prims.of_int (111)) (Prims.of_int (38)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (111)) (Prims.of_int (40))
                              (Prims.of_int (111)) (Prims.of_int (59)))))
                     (Obj.magic (print_term t))
                     (fun uu___1 ->
                        (fun uu___1 -> Obj.magic (print_list_terms' q))
                          uu___1))) uu___)
let (indent : Prims.string -> Prims.string) =
  fun level -> Prims.strcat level " "
let (st_equiv_to_string :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp ->
      Pulse_Syntax_Base.comp ->
        Prims.string ->
          (unit, unit, unit) Pulse_Typing.st_equiv ->
            (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c1 ->
      fun c2 ->
        fun level ->
          fun eq ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                       (Prims.of_int (129)) (Prims.of_int (2))
                       (Prims.of_int (129)) (Prims.of_int (33)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                       (Prims.of_int (120)) (Prims.of_int (4))
                       (Prims.of_int (129)) (Prims.of_int (33)))))
              (Obj.magic
                 (Pulse_Syntax_Printer.term_to_string
                    (Pulse_Syntax_Base.comp_post c2)))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                                  (Prims.of_int (120)) (Prims.of_int (4))
                                  (Prims.of_int (129)) (Prims.of_int (33)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                                  (Prims.of_int (120)) (Prims.of_int (4))
                                  (Prims.of_int (129)) (Prims.of_int (33)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (120))
                                        (Prims.of_int (4))
                                        (Prims.of_int (129))
                                        (Prims.of_int (33)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (120))
                                        (Prims.of_int (4))
                                        (Prims.of_int (129))
                                        (Prims.of_int (33)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Par.fst"
                                              (Prims.of_int (127))
                                              (Prims.of_int (2))
                                              (Prims.of_int (127))
                                              (Prims.of_int (33)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Par.fst"
                                              (Prims.of_int (120))
                                              (Prims.of_int (4))
                                              (Prims.of_int (129))
                                              (Prims.of_int (33)))))
                                     (Obj.magic
                                        (Pulse_Syntax_Printer.term_to_string
                                           (Pulse_Syntax_Base.comp_post c1)))
                                     (fun uu___1 ->
                                        (fun uu___1 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Par.fst"
                                                         (Prims.of_int (120))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (129))
                                                         (Prims.of_int (33)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Par.fst"
                                                         (Prims.of_int (120))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (129))
                                                         (Prims.of_int (33)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Par.fst"
                                                               (Prims.of_int (120))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (129))
                                                               (Prims.of_int (33)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Par.fst"
                                                               (Prims.of_int (120))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (129))
                                                               (Prims.of_int (33)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (32)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (33)))))
                                                            (Obj.magic
                                                               (Pulse_Syntax_Printer.term_to_string
                                                                  (Pulse_Syntax_Base.comp_pre
                                                                    c2)))
                                                            (fun uu___2 ->
                                                               (fun uu___2 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c1)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    fun x3 ->
                                                                    fun x4 ->
                                                                    fun x5 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "st_equiv\n"
                                                                    (Prims.strcat
                                                                    level
                                                                    " pre1: "))
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    "\n"))
                                                                    (Prims.strcat
                                                                    x
                                                                    " pre2: "))
                                                                    (Prims.strcat
                                                                    x1 "\n"))
                                                                    (Prims.strcat
                                                                    x2
                                                                    " post1: "))
                                                                    (Prims.strcat
                                                                    x3 "\n"))
                                                                    (Prims.strcat
                                                                    x4
                                                                    " post2: "))
                                                                    (Prims.strcat
                                                                    x5 "")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    level))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                 uu___2)))
                                                      (fun uu___2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 ->
                                                              uu___2 level))))
                                                (fun uu___2 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        uu___2 uu___1))))
                                          uu___1)))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 -> uu___1 level))))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 -> uu___1 uu___)))) uu___)
let rec (st_typing_to_string' :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        Prims.string ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g ->
               fun t ->
                 fun c ->
                   fun level ->
                     fun ty ->
                       match ty with
                       | Pulse_Typing.T_Abs
                           (g1, x, q, b, u, body, c1, uu___, uu___1) ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> "T_Abs")))
                       | Pulse_Typing.T_STApp
                           (g1, head, uu___, q, res, arg, uu___1, uu___2) ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> "T_STapp")))
                       | Pulse_Typing.T_Return
                           (g1, c1, use_eq, u, t1, e, post, x, uu___, uu___1,
                            uu___2)
                           ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> "T_Return")))
                       | Pulse_Typing.T_Lift (g1, e, c1, c2, uu___, uu___1)
                           ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> "T_Lift")))
                       | Pulse_Typing.T_Bind
                           (g1, e1, e2, c1, c2, b, uu___, c3, ty1, uu___1,
                            ty2, uu___2)
                           ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Par.fst"
                                            (Prims.of_int (143))
                                            (Prims.of_int (6))
                                            (Prims.of_int (143))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Par.fst"
                                            (Prims.of_int (141))
                                            (Prims.of_int (6))
                                            (Prims.of_int (143))
                                            (Prims.of_int (47)))))
                                   (Obj.magic
                                      (st_typing_to_string'
                                         (Pulse_Typing_Env.push_binding g1
                                            uu___
                                            Pulse_Syntax_Base.ppname_default
                                            (Pulse_Syntax_Base.comp_res c1))
                                         (Pulse_Syntax_Naming.open_st_term_nv
                                            e2
                                            ((b.Pulse_Syntax_Base.binder_ppname),
                                              uu___)) c2 (indent level) ty2))
                                   (fun uu___3 ->
                                      (fun uu___3 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (141))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (143))
                                                       (Prims.of_int (47)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (141))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (143))
                                                       (Prims.of_int (47)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Par.fst"
                                                             (Prims.of_int (142))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (142))
                                                             (Prims.of_int (47)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Printf.fst"
                                                             (Prims.of_int (121))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (123))
                                                             (Prims.of_int (44)))))
                                                    (Obj.magic
                                                       (st_typing_to_string'
                                                          g1 e1 c1
                                                          (indent level) ty1))
                                                    (fun uu___4 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___5 ->
                                                            fun x ->
                                                              Prims.strcat
                                                                (Prims.strcat
                                                                   "T_Bind \n ("
                                                                   (Prims.strcat
                                                                    uu___4
                                                                    "); \n ("))
                                                                (Prims.strcat
                                                                   x ")")))))
                                              (fun uu___4 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___5 ->
                                                      uu___4 uu___3))))
                                        uu___3)))
                       | Pulse_Typing.T_TotBind
                           (g1, e1, e2, t1, c2, x, uu___, ty') ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Par.fst"
                                            (Prims.of_int (146))
                                            (Prims.of_int (6))
                                            (Prims.of_int (146))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "prims.fst"
                                            (Prims.of_int (590))
                                            (Prims.of_int (19))
                                            (Prims.of_int (590))
                                            (Prims.of_int (31)))))
                                   (Obj.magic
                                      (st_typing_to_string'
                                         (Pulse_Typing_Env.push_binding g1 x
                                            Pulse_Syntax_Base.ppname_default
                                            t1)
                                         (Pulse_Syntax_Naming.open_st_term_nv
                                            e2 (Pulse_Syntax_Base.v_as_nv x))
                                         c2 (indent level) ty'))
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           Prims.strcat "T_TotBind ("
                                             (Prims.strcat uu___1 ")")))))
                       | Pulse_Typing.T_Frame (g1, e, c1, frame, uu___, ty')
                           ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Par.fst"
                                            (Prims.of_int (151))
                                            (Prims.of_int (6))
                                            (Prims.of_int (151))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Par.fst"
                                            (Prims.of_int (148))
                                            (Prims.of_int (6))
                                            (Prims.of_int (151))
                                            (Prims.of_int (47)))))
                                   (Obj.magic
                                      (st_typing_to_string' g1 e c1
                                         (indent level) ty'))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (148))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (151))
                                                       (Prims.of_int (47)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (148))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (151))
                                                       (Prims.of_int (47)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Par.fst"
                                                             (Prims.of_int (148))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (151))
                                                             (Prims.of_int (47)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Par.fst"
                                                             (Prims.of_int (148))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (151))
                                                             (Prims.of_int (47)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Par.fst"
                                                                   (Prims.of_int (149))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (149))
                                                                   (Prims.of_int (28)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Printf.fst"
                                                                   (Prims.of_int (121))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (123))
                                                                   (Prims.of_int (44)))))
                                                          (Obj.magic
                                                             (Pulse_Syntax_Printer.term_to_string
                                                                frame))
                                                          (fun uu___2 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___3 ->
                                                                  fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "T_Frame (frame="
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    ") (\n"))
                                                                    (Prims.strcat
                                                                    x ""))
                                                                    (Prims.strcat
                                                                    x1 ")")))))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            uu___2 level))))
                                              (fun uu___2 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 ->
                                                      uu___2 uu___1))))
                                        uu___1)))
                       | Pulse_Typing.T_Equiv (g1, e, c1, c', ty', equiv) ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Par.fst"
                                            (Prims.of_int (157))
                                            (Prims.of_int (6))
                                            (Prims.of_int (157))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "prims.fst"
                                            (Prims.of_int (590))
                                            (Prims.of_int (19))
                                            (Prims.of_int (590))
                                            (Prims.of_int (31)))))
                                   (Obj.magic
                                      (st_typing_to_string' g1 e c1
                                         (indent level) ty'))
                                   (fun uu___ ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 ->
                                           Prims.strcat
                                             (Prims.strcat
                                                "T_Equiv (...) (\n"
                                                (Prims.strcat level ""))
                                             (Prims.strcat uu___ ")")))))
                       | Pulse_Typing.T_Par
                           (g1, eL, cL, eR, cR, x, uu___, uu___1, ty1, ty2)
                           ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> "T_Par")))
                       | uu___ ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 -> "Unsupported")))) uu___4
              uu___3 uu___2 uu___1 uu___
let (st_typing_to_string :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun g -> fun t -> fun c -> fun ty -> st_typing_to_string' g t c "" ty
let (create_st_equiv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      Pulse_Syntax_Base.comp_st ->
        unit -> unit -> unit -> (unit, unit, unit) Pulse_Typing.st_equiv)
  =
  fun g ->
    fun c ->
      fun c' ->
        fun equiv_pre ->
          fun typing_pre ->
            fun typing_res ->
              let x = Pulse_Typing_Env.fresh g in
              Pulse_Typing.ST_VPropEquiv (g, c, c', x, (), (), (), (), ())


let rec (replace_frame_emp_with_equiv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t ->
      fun c ->
        fun ty ->
          match ty with
          | Pulse_Typing.T_Frame (g1, e, c', frame, tot_ty, ty') ->
              if Pulse_Syntax_Base.uu___is_Tm_Emp frame.Pulse_Syntax_Base.t
              then
                let pre = Pulse_Syntax_Base.comp_pre c' in
                let st_eq = create_st_equiv g1 c' c () () () in
                Pulse_Typing.T_Equiv
                  (g1, e, c', c, (replace_frame_emp_with_equiv g1 e c' ty'),
                    st_eq)
              else ty
          | Pulse_Typing.T_Equiv (g1, e, c1, c', ty', equiv) ->
              Pulse_Typing.T_Equiv
                (g1, e, c1, c', (replace_frame_emp_with_equiv g1 e c1 ty'),
                  equiv)
          | Pulse_Typing.T_Bind
              (g1, e1, e2, c1, c2, b, x, c3, ty1, tot1, ty2, tot2) ->
              Pulse_Typing.T_Bind
                (g1, e1, e2, c1, c2, b, x, c3,
                  (replace_frame_emp_with_equiv g1 e1 c1 ty1), (),
                  (replace_frame_emp_with_equiv
                     (Pulse_Typing_Env.push_binding g1 x
                        Pulse_Syntax_Base.ppname_default
                        (Pulse_Syntax_Base.comp_res c1))
                     (Pulse_Syntax_Naming.open_st_term_nv e2
                        ((b.Pulse_Syntax_Base.binder_ppname), x)) c2 ty2),
                  tot2)
          | uu___ -> ty
let rec (collect_frames :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          ((Pulse_Syntax_Base.term Prims.list, unit) Prims.dtuple2, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun e ->
               fun c ->
                 fun ty ->
                   match ty with
                   | Pulse_Typing.T_Frame (g1, e1, c', frame, tot_ty, ty') ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> Prims.Mkdtuple2 ([frame], ()))))
                   | Pulse_Typing.T_Equiv (g1, e1, c1, c', ty', equiv) ->
                       Obj.magic (Obj.repr (collect_frames g1 e1 c1 ty'))
                   | Pulse_Typing.T_Bind
                       (g1, e1, e2, c1, c2, b, x, c3, ty1, uu___, ty2,
                        uu___1)
                       ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (253))
                                        (Prims.of_int (23))
                                        (Prims.of_int (253))
                                        (Prims.of_int (41)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (252))
                                        (Prims.of_int (45))
                                        (Prims.of_int (255))
                                        (Prims.of_int (21)))))
                               (Obj.magic (collect_frames g1 e1 c1 ty1))
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     match uu___2 with
                                     | Prims.Mkdtuple2 (l1, tot1) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (254))
                                                       (Prims.of_int (20))
                                                       (Prims.of_int (254))
                                                       (Prims.of_int (38)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (253))
                                                       (Prims.of_int (44))
                                                       (Prims.of_int (255))
                                                       (Prims.of_int (21)))))
                                              (Obj.magic
                                                 (collect_frames
                                                    (Pulse_Typing_Env.push_binding
                                                       g1 x
                                                       Pulse_Syntax_Base.ppname_default
                                                       (Pulse_Syntax_Base.comp_res
                                                          c1))
                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                       e2
                                                       ((b.Pulse_Syntax_Base.binder_ppname),
                                                         x)) c2 ty2))
                                              (fun uu___3 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___4 ->
                                                      match uu___3 with
                                                      | Prims.Mkdtuple2
                                                          (l2, uu___5) ->
                                                          Prims.Mkdtuple2
                                                            ((FStar_List_Tot_Base.op_At
                                                                l1 l2), ())))))
                                    uu___2)))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_V2_Derived.fail
                               "Unable to figure out frame at this leaf")))
            uu___3 uu___2 uu___1 uu___
let (simplify_st_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          ((unit, unit, unit) Pulse_Typing.st_typing, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun e ->
               fun c ->
                 fun ty ->
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> replace_frame_emp_with_equiv g e c ty)))
            uu___3 uu___2 uu___1 uu___
type atom = Pulse_Syntax_Base.term
type 'g typed_list_atoms = (atom, unit) Prims.dtuple2 Prims.list
let rec (compute_intersection_aux :
  Pulse_Typing_Env.env ->
    atom ->
      unit -> atom Prims.list -> (unit typed_list_atoms * atom Prims.list))
  =
  fun g ->
    fun ft ->
      fun ty ->
        fun l ->
          match l with
          | [] -> ([], [])
          | t::q ->
              if Pulse_Syntax_Base.eq_tm t ft
              then ([Prims.Mkdtuple2 (ft, ())], q)
              else
                (let uu___1 = compute_intersection_aux g ft () q in
                 match uu___1 with | (a, b) -> (a, (t :: b)))
let rec (compute_intersection :
  Pulse_Typing_Env.env ->
    unit typed_list_atoms -> atom Prims.list -> unit typed_list_atoms)
  =
  fun g ->
    fun l1 ->
      fun l2 ->
        match l1 with
        | [] -> []
        | t::q ->
            let uu___ =
              compute_intersection_aux g
                (Prims.__proj__Mkdtuple2__item___1 t) () l2 in
            (match uu___ with
             | (a, b) ->
                 FStar_List_Tot_Base.op_At a (compute_intersection g q b))
let rec (vprop_as_list_typed :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term -> unit -> unit typed_list_atoms)
  =
  fun g ->
    fun vp ->
      fun ty ->
        match vp.Pulse_Syntax_Base.t with
        | Pulse_Syntax_Base.Tm_Emp -> []
        | Pulse_Syntax_Base.Tm_Star (vp0, vp1) ->
            FStar_List_Tot_Base.op_At (vprop_as_list_typed g vp0 ())
              (vprop_as_list_typed g vp1 ())
        | uu___ -> [Prims.Mkdtuple2 (vp, ())]
let (compute_intersection_list :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term Prims.list ->
      unit ->
        ((atom, unit) Prims.dtuple2 Prims.list, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun l ->
             fun ty ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       match l with
                       | [] -> []
                       | t::q ->
                           FStar_List_Tot_Base.fold_left
                             (compute_intersection g)
                             (vprop_as_list_typed g t ())
                             (FStar_List_Tot_Base.map
                                Pulse_Checker_VPropEquiv.vprop_as_list q))))
          uu___2 uu___1 uu___
let rec (list_of_FStar_term_to_string :
  FStar_Reflection_Types.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun l ->
       match l with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | t::q ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                            (Prims.of_int (426)) (Prims.of_int (12))
                            (Prims.of_int (426)) (Prims.of_int (30)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                            (Prims.of_int (426)) (Prims.of_int (12))
                            (Prims.of_int (426)) (Prims.of_int (70)))))
                   (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string t))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Par.fst"
                                       (Prims.of_int (426))
                                       (Prims.of_int (33))
                                       (Prims.of_int (426))
                                       (Prims.of_int (70)))))
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
                                             "Pulse.Checker.Par.fst"
                                             (Prims.of_int (426))
                                             (Prims.of_int (40))
                                             (Prims.of_int (426))
                                             (Prims.of_int (70)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (list_of_FStar_term_to_string q))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat ", " uu___1))))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> Prims.strcat uu___ uu___1))))
                        uu___)))) uu___
let (adapt_st_comp :
  Pulse_Syntax_Base.st_comp ->
    Pulse_Syntax_Base.vprop ->
      Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.st_comp)
  =
  fun c ->
    fun pre ->
      fun post ->
        {
          Pulse_Syntax_Base.u = (c.Pulse_Syntax_Base.u);
          Pulse_Syntax_Base.res = (c.Pulse_Syntax_Base.res);
          Pulse_Syntax_Base.pre = pre;
          Pulse_Syntax_Base.post = post
        }
let (remove_from_vprop :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        unit ->
          ((Pulse_Syntax_Base.term, unit, unit) FStar_Pervasives.dtuple3,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun inter ->
        fun ctxt_typing ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                     (Prims.of_int (516)) (Prims.of_int (8))
                     (Prims.of_int (516)) (Prims.of_int (41)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                     (Prims.of_int (516)) (Prims.of_int (2))
                     (Prims.of_int (518)) (Prims.of_int (69)))))
            (Obj.magic
               (Pulse_Checker_Framing.check_frameable g ctxt () inter))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | FStar_Pervasives.Inl x ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> x)))
                  | FStar_Pervasives.Inr uu___1 ->
                      Obj.magic
                        (Obj.repr
                           (Pulse_Typing_Env.fail g
                              FStar_Pervasives_Native.None
                              "Failure to remove intersection from frame...")))
                 uu___)
let rec (extract_common_frame :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.term ->
          unit ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              ((unit, unit, unit) Pulse_Typing.st_typing, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun c ->
        fun inter ->
          fun inter_typed ->
            fun ty ->
              match ty with
              | Pulse_Typing.T_Frame (g1, e, c0, frame, tot_ty, ty') ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                             (Prims.of_int (526)) (Prims.of_int (35))
                             (Prims.of_int (526)) (Prims.of_int (65)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                             (Prims.of_int (525)) (Prims.of_int (38))
                             (Prims.of_int (548)) (Prims.of_int (28)))))
                    (Obj.magic (remove_from_vprop g1 frame inter ()))
                    (fun uu___ ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            match uu___ with
                            | FStar_Pervasives.Mkdtuple3
                                (f1, tot_ty1, eq_21_f) ->
                                Pulse_Typing.T_Equiv
                                  (g1, e,
                                    (Pulse_Typing.add_frame
                                       (Pulse_Typing.add_frame c0 f1) inter),
                                    c,
                                    (Pulse_Typing.T_Frame
                                       (g1, e,
                                         (Pulse_Typing.add_frame c0 f1),
                                         inter, (),
                                         (Pulse_Typing.T_Frame
                                            (g1, e, c0, f1, (), ty')))),
                                    (create_st_equiv g1
                                       (Pulse_Typing.add_frame
                                          (Pulse_Typing.add_frame c0 f1)
                                          inter) c () () ()))))
              | Pulse_Typing.T_Equiv (g1, e, c1, c', ty', equiv) ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                             (Prims.of_int (559)) (Prims.of_int (19))
                             (Prims.of_int (559)) (Prims.of_int (57)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                             (Prims.of_int (559)) (Prims.of_int (2))
                             (Prims.of_int (559)) (Prims.of_int (63)))))
                    (Obj.magic (extract_common_frame g e c1 inter () ty'))
                    (fun uu___ ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            Pulse_Typing.T_Equiv
                              (g1, e, c1, c', uu___, equiv)))
              | Pulse_Typing.T_Bind
                  (g1, e1, e2, c1, c2, b, x, c3, ty1, tot1, ty2, tot2) ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                             (Prims.of_int (563)) (Prims.of_int (6))
                             (Prims.of_int (563)) (Prims.of_int (78)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                             (Prims.of_int (564)) (Prims.of_int (2))
                             (Prims.of_int (564)) (Prims.of_int (127)))))
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))
                    (fun uu___ ->
                       (fun ntyped ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (564))
                                        (Prims.of_int (29))
                                        (Prims.of_int (564))
                                        (Prims.of_int (67)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (564))
                                        (Prims.of_int (2))
                                        (Prims.of_int (564))
                                        (Prims.of_int (127)))))
                               (Obj.magic
                                  (extract_common_frame g e1 c1 inter () ty1))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (564))
                                                   (Prims.of_int (73))
                                                   (Prims.of_int (564))
                                                   (Prims.of_int (122)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (564))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (564))
                                                   (Prims.of_int (127)))))
                                          (Obj.magic
                                             (extract_common_frame
                                                (Pulse_Typing_Env.push_binding
                                                   g x
                                                   Pulse_Syntax_Base.ppname_default
                                                   (Pulse_Syntax_Base.comp_res
                                                      c1))
                                                (Pulse_Syntax_Naming.open_st_term_nv
                                                   e2
                                                   ((b.Pulse_Syntax_Base.binder_ppname),
                                                     x)) c2 inter () ty2))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Pulse_Typing.T_Bind
                                                    (g1, e1, e2, c1, c2, b,
                                                      x, c3, uu___, (),
                                                      uu___1, tot2))))) uu___)))
                         uu___)
              | uu___ ->
                  Pulse_Typing_Env.fail g FStar_Pervasives_Native.None
                    "No common frame to extract..."
let rec (list_as_vprop_typed :
  Pulse_Typing_Env.env ->
    (atom, unit) Prims.dtuple2 Prims.list ->
      (Pulse_Syntax_Base.term, unit) Prims.dtuple2)
  =
  fun g ->
    fun l ->
      match l with
      | [] -> Prims.Mkdtuple2 (Pulse_Syntax_Base.tm_emp, ())
      | (Prims.Mkdtuple2 (t, ty))::q ->
          let uu___ = list_as_vprop_typed g q in
          (match uu___ with
           | Prims.Mkdtuple2 (qt, qty) ->
               Prims.Mkdtuple2 ((Pulse_Syntax_Base.tm_star t qt), ()))
let (infer_frame_and_typecheck :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Prims.bool ->
        Pulse_Syntax_Base.st_term ->
          unit ->
            unit Pulse_Typing.post_hint_opt ->
              (Prims.bool -> Pulse_Checker_Common.check_t) ->
                ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                   Pulse_Syntax_Base.vprop, unit,
                   ((unit, unit, unit) Pulse_Typing.st_typing * unit))
                   FStar_Pervasives.dtuple5,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun allow_inst ->
        fun t ->
          fun ctxt_typing ->
            fun post_hint ->
              fun check' ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (724)) (Prims.of_int (31))
                           (Prims.of_int (724)) (Prims.of_int (74)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (722)) Prims.int_one
                           (Prims.of_int (735)) (Prims.of_int (64)))))
                  (Obj.magic
                     (check' allow_inst g t ctxt ()
                        FStar_Pervasives_Native.None))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | FStar_Pervasives.Mkdtuple3 (t1, c, big_typing) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Par.fst"
                                          (Prims.of_int (726))
                                          (Prims.of_int (11))
                                          (Prims.of_int (726))
                                          (Prims.of_int (40)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Par.fst"
                                          (Prims.of_int (726))
                                          (Prims.of_int (43))
                                          (Prims.of_int (735))
                                          (Prims.of_int (64)))))
                                 (Obj.magic
                                    (simplify_st_typing g t1 c big_typing))
                                 (fun uu___1 ->
                                    (fun ty ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Par.fst"
                                                     (Prims.of_int (728))
                                                     (Prims.of_int (35))
                                                     (Prims.of_int (728))
                                                     (Prims.of_int (52)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Par.fst"
                                                     (Prims.of_int (726))
                                                     (Prims.of_int (43))
                                                     (Prims.of_int (735))
                                                     (Prims.of_int (64)))))
                                            (Obj.magic
                                               (collect_frames g t1 c ty))
                                            (fun uu___1 ->
                                               (fun uu___1 ->
                                                  match uu___1 with
                                                  | Prims.Mkdtuple2
                                                      (frames, typing_frame)
                                                      ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (66)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (64)))))
                                                           (Obj.magic
                                                              (compute_intersection_list
                                                                 g frames ()))
                                                           (fun uu___2 ->
                                                              (fun inter_list
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    list_as_vprop_typed
                                                                    g
                                                                    inter_list))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (frame,
                                                                    frame_typed)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    (remove_from_vprop
                                                                    g ctxt
                                                                    frame ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (inferred_pre,
                                                                    typing_pre,
                                                                    equiv_pre)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g t1
                                                                    inferred_pre
                                                                    ()
                                                                    post_hint))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t2, c1,
                                                                    typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (t2, c1,
                                                                    frame,
                                                                    (),
                                                                    (typing,
                                                                    ()))))))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                uu___2)))
                                                 uu___1))) uu___1))) uu___)
let (check_par_compute_preconditions :
  Prims.bool ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.st_term ->
            Pulse_Syntax_Base.vprop ->
              Pulse_Syntax_Base.vprop ->
                unit Pulse_Typing.post_hint_opt ->
                  (Prims.bool -> Pulse_Checker_Common.check_t) ->
                    ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                       Pulse_Syntax_Base.vprop, unit,
                       (unit, unit, unit) Pulse_Typing.st_typing)
                       FStar_Pervasives.dtuple5,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun pre ->
        fun pre_typing ->
          fun eL ->
            fun preL ->
              fun preR ->
                fun postL_hint ->
                  fun check' ->
                    if
                      (Pulse_Syntax_Base.uu___is_Tm_Unknown
                         preL.Pulse_Syntax_Base.t)
                        &&
                        (Pulse_Syntax_Base.uu___is_Tm_Unknown
                           preR.Pulse_Syntax_Base.t)
                    then
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                                 (Prims.of_int (766)) (Prims.of_int (60))
                                 (Prims.of_int (766)) (Prims.of_int (128)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                                 (Prims.of_int (763)) (Prims.of_int (52))
                                 (Prims.of_int (767)) (Prims.of_int (48)))))
                        (Obj.magic
                           (infer_frame_and_typecheck g pre allow_inst eL ()
                              postL_hint check'))
                        (fun uu___ ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 ->
                                match uu___ with
                                | FStar_Pervasives.Mkdtuple5
                                    (eL1, cL, preR1, preR_typing,
                                     (eL_typing, uu___2))
                                    ->
                                    FStar_Pervasives.Mkdtuple5
                                      (eL1, cL, preR1, (), eL_typing)))
                    else
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                                 (Prims.of_int (771)) (Prims.of_int (36))
                                 (Prims.of_int (771)) (Prims.of_int (81)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                                 (Prims.of_int (769)) (Prims.of_int (4))
                                 (Prims.of_int (787)) (Prims.of_int (3)))))
                        (Obj.magic
                           (Pulse_Checker_Pure.check_term_with_expected_type
                              g preL Pulse_Syntax_Base.tm_vprop))
                        (fun uu___1 ->
                           (fun uu___1 ->
                              match uu___1 with
                              | Prims.Mkdtuple2 (preL1, preL_typing) ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Par.fst"
                                                (Prims.of_int (772))
                                                (Prims.of_int (36))
                                                (Prims.of_int (772))
                                                (Prims.of_int (90)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Par.fst"
                                                (Prims.of_int (771))
                                                (Prims.of_int (84))
                                                (Prims.of_int (786))
                                                (Prims.of_int (48)))))
                                       (Obj.magic
                                          (check' allow_inst g eL preL1 ()
                                             postL_hint))
                                       (fun uu___2 ->
                                          (fun uu___2 ->
                                             match uu___2 with
                                             | FStar_Pervasives.Mkdtuple3
                                                 (eL1, cL, eL_typing) ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Par.fst"
                                                               (Prims.of_int (774))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (785))
                                                               (Prims.of_int (7)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Par.fst"
                                                               (Prims.of_int (772))
                                                               (Prims.of_int (93))
                                                               (Prims.of_int (786))
                                                               (Prims.of_int (48)))))
                                                      (if
                                                         Pulse_Syntax_Base.uu___is_Tm_Unknown
                                                           preR.Pulse_Syntax_Base.t
                                                       then
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (778))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (778))
                                                                    (Prims.of_int (76)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (775))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (779))
                                                                    (Prims.of_int (33)))))
                                                              (Obj.magic
                                                                 (remove_from_vprop
                                                                    g pre
                                                                    preL1 ()))
                                                              (fun uu___3 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (preR1,
                                                                    preR_typing,
                                                                    uu___5)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (preR1,
                                                                    ()))))
                                                       else
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (783))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (783))
                                                                    (Prims.of_int (85)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (780))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (784))
                                                                    (Prims.of_int (35)))))
                                                              (Obj.magic
                                                                 (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g preR
                                                                    Pulse_Syntax_Base.tm_vprop))
                                                              (fun uu___4 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (preR1,
                                                                    preR_typing)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (preR1,
                                                                    ())))))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              match uu___3
                                                              with
                                                              | Prims.Mkdtuple2
                                                                  (preR1,
                                                                   preR_typing)
                                                                  ->
                                                                  FStar_Pervasives.Mkdtuple5
                                                                    (eL1, cL,
                                                                    preR1,
                                                                    (),
                                                                    eL_typing)))))
                                            uu___2))) uu___1)
let (check_par' :
  Prims.bool ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Typing.post_hint_opt ->
              (Prims.bool -> Pulse_Checker_Common.check_t) ->
                ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun check' ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (799)) (Prims.of_int (10))
                           (Prims.of_int (799)) (Prims.of_int (44)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (799)) (Prims.of_int (47))
                           (Prims.of_int (827)) (Prims.of_int (52)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Checker_Pure.push_context "check_par"
                          t.Pulse_Syntax_Base.range2 g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Par.fst"
                                      (Prims.of_int (800))
                                      (Prims.of_int (84))
                                      (Prims.of_int (800))
                                      (Prims.of_int (90)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Par.fst"
                                      (Prims.of_int (799))
                                      (Prims.of_int (47))
                                      (Prims.of_int (827))
                                      (Prims.of_int (52)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> t.Pulse_Syntax_Base.term1))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | Pulse_Syntax_Base.Tm_Par
                                       { Pulse_Syntax_Base.pre1 = preL;
                                         Pulse_Syntax_Base.body11 = eL;
                                         Pulse_Syntax_Base.post11 = postL;
                                         Pulse_Syntax_Base.pre2 = preR;
                                         Pulse_Syntax_Base.body21 = eR;
                                         Pulse_Syntax_Base.post2 = postR;_}
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Par.fst"
                                                     (Prims.of_int (801))
                                                     (Prims.of_int (36))
                                                     (Prims.of_int (801))
                                                     (Prims.of_int (109)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Par.fst"
                                                     (Prims.of_int (801))
                                                     (Prims.of_int (112))
                                                     (Prims.of_int (827))
                                                     (Prims.of_int (52)))))
                                            (if
                                               Pulse_Syntax_Base.uu___is_Tm_Unknown
                                                 postL.Pulse_Syntax_Base.t
                                             then
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          FStar_Pervasives_Native.None)))
                                             else
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Par.fst"
                                                                (Prims.of_int (801))
                                                                (Prims.of_int (79))
                                                                (Prims.of_int (801))
                                                                (Prims.of_int (109)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Par.fst"
                                                                (Prims.of_int (801))
                                                                (Prims.of_int (74))
                                                                (Prims.of_int (801))
                                                                (Prims.of_int (109)))))
                                                       (Obj.magic
                                                          (Pulse_Checker_Common.intro_post_hint
                                                             g1
                                                             FStar_Pervasives_Native.None
                                                             postL))
                                                       (fun uu___2 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___3 ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu___2)))))
                                            (fun uu___1 ->
                                               (fun postL_hint ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Par.fst"
                                                                (Prims.of_int (805))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (805))
                                                                (Prims.of_int (94)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Par.fst"
                                                                (Prims.of_int (801))
                                                                (Prims.of_int (112))
                                                                (Prims.of_int (827))
                                                                (Prims.of_int (52)))))
                                                       (Obj.magic
                                                          (check_par_compute_preconditions
                                                             allow_inst g1
                                                             pre () eL preL
                                                             preR postL_hint
                                                             check'))
                                                       (fun uu___1 ->
                                                          (fun uu___1 ->
                                                             match uu___1
                                                             with
                                                             | FStar_Pervasives.Mkdtuple5
                                                                 (eL1, cL,
                                                                  preR1,
                                                                  preR_typing,
                                                                  eL_typing)
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (807))
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (827))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (807))
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (827))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    uu___1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    if
                                                                    Pulse_Syntax_Base.uu___is_C_ST
                                                                    cL
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (810))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (810))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    "LEFT PRE:"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (812))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    cL)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (812))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (812))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    "RIGHT PRE:"))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    preR1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___6))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (814))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (814))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (814))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g1 eL1 cL
                                                                    eL_typing))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    cL_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (54)))))
                                                                    (if
                                                                    Pulse_Syntax_Base.uu___is_Tm_Unknown
                                                                    postR.Pulse_Syntax_Base.t
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.intro_post_hint
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    postR))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___8)))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    postR_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g1 eR
                                                                    preR1 ()
                                                                    postR_hint))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eR1, cR,
                                                                    eR_typing)
                                                                    ->
                                                                    if
                                                                    (Pulse_Syntax_Base.uu___is_C_ST
                                                                    cR) &&
                                                                    (Pulse_Syntax_Base.eq_univ
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    cL)
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    cR))
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (825))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g1 eR1 cR
                                                                    eR_typing))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    cR_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (825))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (821))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (821))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (822))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (825))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Typing.T_Par
                                                                    (g1, eL1,
                                                                    cL, eR1,
                                                                    cR, x,
                                                                    cL_typing,
                                                                    cR_typing,
                                                                    eL_typing,
                                                                    eR_typing)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (822))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (822))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (822))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (825))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Framing.try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre1
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.body11
                                                                    = eL1;
                                                                    Pulse_Syntax_Base.post11
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.pre2
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.body21
                                                                    = eR1;
                                                                    Pulse_Syntax_Base.post2
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_par
                                                                    cL cR x)
                                                                    d))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    x1 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.repack
                                                                    g pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre1
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.body11
                                                                    = eL1;
                                                                    Pulse_Syntax_Base.post11
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.pre2
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.body21
                                                                    = eR1;
                                                                    Pulse_Syntax_Base.post2
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown
                                                                    })) x1
                                                                    post_hint)
                                                                    | 
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Failure in main function..."))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (eR1.Pulse_Syntax_Base.range2))
                                                                    "par: cR is not stt"))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (eL1.Pulse_Syntax_Base.range2))
                                                                    "par: cL is not stt"))
                                                                    uu___2)))
                                                            uu___1))) uu___1)))
                                  uu___))) uu___)
let rec (check_par :
  Prims.bool ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Typing.post_hint_opt ->
              (Prims.bool -> Pulse_Checker_Common.check_t) ->
                ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun check' ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (841)) (Prims.of_int (10))
                           (Prims.of_int (841)) (Prims.of_int (44)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (841)) (Prims.of_int (47))
                           (Prims.of_int (849)) (Prims.of_int (61)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Checker_Pure.push_context "check_par"
                          t.Pulse_Syntax_Base.range2 g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Par.fst"
                                      (Prims.of_int (842))
                                      (Prims.of_int (84))
                                      (Prims.of_int (842))
                                      (Prims.of_int (90)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Par.fst"
                                      (Prims.of_int (841))
                                      (Prims.of_int (47))
                                      (Prims.of_int (849))
                                      (Prims.of_int (61)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> t.Pulse_Syntax_Base.term1))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | Pulse_Syntax_Base.Tm_Par
                                       { Pulse_Syntax_Base.pre1 = preL;
                                         Pulse_Syntax_Base.body11 = eL;
                                         Pulse_Syntax_Base.post11 = postL;
                                         Pulse_Syntax_Base.pre2 = preR;
                                         Pulse_Syntax_Base.body21 = eR;
                                         Pulse_Syntax_Base.post2 = postR;_}
                                       ->
                                       if
                                         (Pulse_Syntax_Base.uu___is_Tm_Unknown
                                            preL.Pulse_Syntax_Base.t)
                                           &&
                                           (Prims.op_Negation
                                              (Pulse_Syntax_Base.uu___is_Tm_Unknown
                                                 preR.Pulse_Syntax_Base.t))
                                       then
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (846))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (846))
                                                       (Prims.of_int (113)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (847))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (847))
                                                       (Prims.of_int (62)))))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    {
                                                      Pulse_Syntax_Base.term1
                                                        =
                                                        (Pulse_Syntax_Base.Tm_Par
                                                           {
                                                             Pulse_Syntax_Base.pre1
                                                               = preR;
                                                             Pulse_Syntax_Base.body11
                                                               = eR;
                                                             Pulse_Syntax_Base.post11
                                                               = postR;
                                                             Pulse_Syntax_Base.pre2
                                                               = preL;
                                                             Pulse_Syntax_Base.body21
                                                               = eL;
                                                             Pulse_Syntax_Base.post2
                                                               = postL
                                                           });
                                                      Pulse_Syntax_Base.range2
                                                        = FStar_Range.range_0
                                                    }))
                                              (fun uu___1 ->
                                                 (fun t' ->
                                                    Obj.magic
                                                      (check_par' allow_inst
                                                         g1 t' pre ()
                                                         post_hint check'))
                                                   uu___1))
                                       else
                                         Obj.magic
                                           (check_par' allow_inst g1 t pre ()
                                              post_hint check')) uu___)))
                       uu___)