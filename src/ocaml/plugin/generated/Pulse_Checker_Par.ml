open Prims
let (print_term :
  Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Par.fst" (Prims.of_int (22))
               (Prims.of_int (12)) (Prims.of_int (22)) (Prims.of_int (30)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Par.fst" (Prims.of_int (22))
               (Prims.of_int (4)) (Prims.of_int (22)) (Prims.of_int (30)))))
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
                   (Prims.of_int (27)) (Prims.of_int (11))
                   (Prims.of_int (27)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                   (Prims.of_int (27)) (Prims.of_int (25))
                   (Prims.of_int (27)) (Prims.of_int (58)))))
          (Obj.magic (FStar_Tactics_V2_Builtins.print ", "))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (27)) (Prims.of_int (25))
                              (Prims.of_int (27)) (Prims.of_int (37)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (27)) (Prims.of_int (39))
                              (Prims.of_int (27)) (Prims.of_int (58)))))
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
                   (Prims.of_int (32)) (Prims.of_int (13))
                   (Prims.of_int (32)) (Prims.of_int (24)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                   (Prims.of_int (32)) (Prims.of_int (26))
                   (Prims.of_int (32)) (Prims.of_int (59)))))
          (Obj.magic (FStar_Tactics_V2_Builtins.print "["))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (32)) (Prims.of_int (26))
                              (Prims.of_int (32)) (Prims.of_int (38)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (32)) (Prims.of_int (40))
                              (Prims.of_int (32)) (Prims.of_int (59)))))
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
                       (Prims.of_int (50)) (Prims.of_int (2))
                       (Prims.of_int (50)) (Prims.of_int (33)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                       (Prims.of_int (41)) (Prims.of_int (4))
                       (Prims.of_int (50)) (Prims.of_int (33)))))
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
                                  (Prims.of_int (41)) (Prims.of_int (4))
                                  (Prims.of_int (50)) (Prims.of_int (33)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                                  (Prims.of_int (41)) (Prims.of_int (4))
                                  (Prims.of_int (50)) (Prims.of_int (33)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (41))
                                        (Prims.of_int (4))
                                        (Prims.of_int (50))
                                        (Prims.of_int (33)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (41))
                                        (Prims.of_int (4))
                                        (Prims.of_int (50))
                                        (Prims.of_int (33)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Par.fst"
                                              (Prims.of_int (48))
                                              (Prims.of_int (2))
                                              (Prims.of_int (48))
                                              (Prims.of_int (33)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Par.fst"
                                              (Prims.of_int (41))
                                              (Prims.of_int (4))
                                              (Prims.of_int (50))
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
                                                         (Prims.of_int (41))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (50))
                                                         (Prims.of_int (33)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Par.fst"
                                                         (Prims.of_int (41))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (50))
                                                         (Prims.of_int (33)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Par.fst"
                                                               (Prims.of_int (41))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (50))
                                                               (Prims.of_int (33)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Par.fst"
                                                               (Prims.of_int (41))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (50))
                                                               (Prims.of_int (33)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (32)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (50))
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
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (44))
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
                                            (Prims.of_int (64))
                                            (Prims.of_int (6))
                                            (Prims.of_int (64))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Par.fst"
                                            (Prims.of_int (62))
                                            (Prims.of_int (6))
                                            (Prims.of_int (64))
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
                                                       (Prims.of_int (62))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (64))
                                                       (Prims.of_int (47)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (62))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (64))
                                                       (Prims.of_int (47)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Par.fst"
                                                             (Prims.of_int (63))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (63))
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
                                            (Prims.of_int (68))
                                            (Prims.of_int (6))
                                            (Prims.of_int (68))
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
                                            (Prims.of_int (74))
                                            (Prims.of_int (6))
                                            (Prims.of_int (74))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Par.fst"
                                            (Prims.of_int (71))
                                            (Prims.of_int (6))
                                            (Prims.of_int (74))
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
                                                       (Prims.of_int (71))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (74))
                                                       (Prims.of_int (47)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (71))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (74))
                                                       (Prims.of_int (47)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Par.fst"
                                                             (Prims.of_int (71))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (74))
                                                             (Prims.of_int (47)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Par.fst"
                                                             (Prims.of_int (71))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (74))
                                                             (Prims.of_int (47)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Par.fst"
                                                                   (Prims.of_int (72))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (72))
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
                                            (Prims.of_int (81))
                                            (Prims.of_int (6))
                                            (Prims.of_int (81))
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
        unit -> (unit, unit, unit) Pulse_Typing.st_equiv)
  =
  fun g ->
    fun c ->
      fun c' ->
        fun equiv_pre ->
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
                let st_eq = create_st_equiv g1 c' c () in
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
          (Pulse_Syntax_Base.term Prims.list, unit)
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
                               (fun uu___ -> [frame])))
                   | Pulse_Typing.T_Equiv (g1, e1, c1, c', ty', equiv) ->
                       Obj.magic (Obj.repr (collect_frames g1 e1 c1 ty'))
                   | Pulse_Typing.T_Bind
                       (g1, e1, e2, c1, c2, b, x, c3, ty1, tot1, ty2, tot2)
                       ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (153))
                                        (Prims.of_int (52))
                                        (Prims.of_int (153))
                                        (Prims.of_int (70)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (153))
                                        (Prims.of_int (52))
                                        (Prims.of_int (153))
                                        (Prims.of_int (91)))))
                               (Obj.magic (collect_frames g1 e1 c1 ty1))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (153))
                                                   (Prims.of_int (73))
                                                   (Prims.of_int (153))
                                                   (Prims.of_int (91)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (153))
                                                   (Prims.of_int (52))
                                                   (Prims.of_int (153))
                                                   (Prims.of_int (91)))))
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
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  FStar_List_Tot_Base.op_At
                                                    uu___ uu___1)))) uu___)))
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
let (deq :
  Pulse_Syntax_Base.host_term -> Pulse_Syntax_Base.host_term -> Prims.bool) =
  fun a -> fun b -> FStar_Reflection_V2_TermEq.term_eq_dec a b
let (delta :
  Pulse_Syntax_Base.host_term -> Pulse_Syntax_Base.host_term -> Prims.nat) =
  fun a -> fun b -> if deq a b then Prims.int_one else Prims.int_zero
let rec (countt :
  Pulse_Syntax_Base.host_term Prims.list ->
    Pulse_Syntax_Base.host_term -> Prims.nat)
  =
  fun l ->
    fun x ->
      match l with
      | [] -> Prims.int_zero
      | t::q -> (delta t x) + (countt q x)
let rec (compute_intersection_aux :
  Pulse_Syntax_Base.host_term ->
    Pulse_Syntax_Base.host_term Prims.list ->
      (Pulse_Syntax_Base.host_term Prims.list * Pulse_Syntax_Base.host_term
        Prims.list))
  =
  fun ft ->
    fun l ->
      match l with
      | [] -> ([], [])
      | t::q ->
          if deq ft t
          then ([t], q)
          else
            (let uu___1 = compute_intersection_aux ft q in
             match uu___1 with | (a, b) -> (a, (t :: b)))
let rec (compute_intersection :
  Pulse_Syntax_Base.host_term Prims.list ->
    Pulse_Syntax_Base.host_term Prims.list ->
      Pulse_Syntax_Base.host_term Prims.list)
  =
  fun l1 ->
    fun l2 ->
      match l1 with
      | [] -> []
      | t::q ->
          let uu___ = compute_intersection_aux t l2 in
          (match uu___ with
           | (a, b) -> FStar_List_Tot_Base.op_At a (compute_intersection q b))
let rec (term_to_list :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.host_term Prims.list) =
  fun t ->
    match t.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_FStar ft -> [ft]
    | Pulse_Syntax_Base.Tm_Star (l, r) ->
        FStar_List_Tot_Base.op_At (term_to_list l) (term_to_list r)
    | uu___ -> []
let (compute_intersection_list :
  Pulse_Syntax_Base.term Prims.list -> Pulse_Syntax_Base.host_term Prims.list)
  =
  fun l ->
    match FStar_List_Tot_Base.map term_to_list l with
    | [] -> []
    | t::q -> FStar_List_Tot_Base.fold_left compute_intersection t q
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
                            (Prims.of_int (241)) (Prims.of_int (12))
                            (Prims.of_int (241)) (Prims.of_int (30)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                            (Prims.of_int (241)) (Prims.of_int (12))
                            (Prims.of_int (241)) (Prims.of_int (70)))))
                   (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string t))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Par.fst"
                                       (Prims.of_int (241))
                                       (Prims.of_int (33))
                                       (Prims.of_int (241))
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
                                             (Prims.of_int (241))
                                             (Prims.of_int (40))
                                             (Prims.of_int (241))
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
let rec (remove_host_term_from_term :
  Pulse_Syntax_Base.host_term ->
    Pulse_Syntax_Base.term -> (Prims.bool * Pulse_Syntax_Base.term))
  =
  fun ht ->
    fun t ->
      match t.Pulse_Syntax_Base.t with
      | Pulse_Syntax_Base.Tm_FStar ft ->
          if deq ft ht
          then
            (true,
              (Pulse_Syntax_Base.with_range Pulse_Syntax_Base.Tm_Emp
                 t.Pulse_Syntax_Base.range1))
          else (false, t)
      | Pulse_Syntax_Base.Tm_Star (l, r) ->
          let uu___ = remove_host_term_from_term ht l in
          (match uu___ with
           | (b, l') ->
               if b
               then
                 (true,
                   (Pulse_Syntax_Base.with_range
                      (Pulse_Syntax_Base.Tm_Star (l', r))
                      t.Pulse_Syntax_Base.range1))
               else
                 (let uu___2 = remove_host_term_from_term ht r in
                  match uu___2 with
                  | (b', r') ->
                      if b'
                      then
                        (true,
                          (Pulse_Syntax_Base.with_range
                             (Pulse_Syntax_Base.Tm_Star (l, r'))
                             t.Pulse_Syntax_Base.range1))
                      else (false, t)))
      | uu___ -> (false, t)
let rec (remove_from_vprop :
  Pulse_Syntax_Base.host_term Prims.list ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun l ->
         fun t ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           | ht::q ->
               Obj.magic
                 (Obj.repr
                    (remove_from_vprop q
                       (FStar_Pervasives_Native.__proj__Mktuple2__item___2
                          (remove_host_term_from_term ht t))))) uu___1 uu___
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
let (add_range :
  Pulse_Syntax_Base.range ->
    Pulse_Syntax_Base.host_term -> Pulse_Syntax_Base.term)
  =
  fun r ->
    fun t -> Pulse_Syntax_Base.with_range (Pulse_Syntax_Base.Tm_FStar t) r
let (star_with_range :
  Pulse_Syntax_Base.range ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun r ->
    fun a ->
      fun b ->
        Pulse_Syntax_Base.with_range (Pulse_Syntax_Base.Tm_Star (a, b)) r
let (from_list_to_term :
  Pulse_Syntax_Base.range ->
    Pulse_Syntax_Base.host_term Prims.list -> Pulse_Syntax_Base.term)
  =
  fun r ->
    fun l ->
      let l' = FStar_List_Tot_Base.map (add_range r) l in
      let temp = Pulse_Syntax_Base.with_range Pulse_Syntax_Base.Tm_Emp r in
      FStar_List_Tot_Base.fold_left (star_with_range r) temp l'
let rec (extract_common_frame :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.host_term Prims.list ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            ((unit, unit, unit) Pulse_Typing.st_typing, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun c ->
        fun inter ->
          fun ty ->
            match ty with
            | Pulse_Typing.T_Frame (g1, e, c0, frame, tot_ty, ty') ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (277)) (Prims.of_int (11))
                           (Prims.of_int (277)) (Prims.of_int (40)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (298)) (Prims.of_int (2))
                           (Prims.of_int (298)) (Prims.of_int (28)))))
                  (Obj.magic (remove_from_vprop inter frame))
                  (fun f1 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          Pulse_Typing.T_Equiv
                            (g1, e,
                              (Pulse_Typing.add_frame
                                 (Pulse_Typing.add_frame c0 f1)
                                 (from_list_to_term
                                    frame.Pulse_Syntax_Base.range1 inter)),
                              c,
                              (Pulse_Typing.T_Frame
                                 (g1, e, (Pulse_Typing.add_frame c0 f1),
                                   (from_list_to_term
                                      frame.Pulse_Syntax_Base.range1 inter),
                                   (),
                                   (Pulse_Typing.T_Frame
                                      (g1, e, c0, f1, (), ty')))),
                              (create_st_equiv g1
                                 (Pulse_Typing.add_frame
                                    (Pulse_Typing.add_frame c0 f1)
                                    (from_list_to_term
                                       frame.Pulse_Syntax_Base.range1 inter))
                                 c ()))))
            | Pulse_Typing.T_Equiv (g1, e, c1, c', ty', equiv) ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (309)) (Prims.of_int (19))
                           (Prims.of_int (309)) (Prims.of_int (51)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (309)) (Prims.of_int (2))
                           (Prims.of_int (309)) (Prims.of_int (57)))))
                  (Obj.magic (extract_common_frame g1 e c1 inter ty'))
                  (fun uu___ ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          Pulse_Typing.T_Equiv (g1, e, c1, c', uu___, equiv)))
            | Pulse_Typing.T_Bind
                (g1, e1, e2, c1, c2, b, x, c3, ty1, tot1, ty2, tot2) ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (311)) (Prims.of_int (29))
                           (Prims.of_int (311)) (Prims.of_int (61)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (311)) (Prims.of_int (2))
                           (Prims.of_int (311)) (Prims.of_int (104)))))
                  (Obj.magic (extract_common_frame g1 e1 c1 inter ty1))
                  (fun uu___ ->
                     (fun uu___ ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Par.fst"
                                      (Prims.of_int (311))
                                      (Prims.of_int (67))
                                      (Prims.of_int (311))
                                      (Prims.of_int (99)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Par.fst"
                                      (Prims.of_int (311)) (Prims.of_int (2))
                                      (Prims.of_int (311))
                                      (Prims.of_int (104)))))
                             (Obj.magic
                                (extract_common_frame
                                   (Pulse_Typing_Env.push_binding g1 x
                                      Pulse_Syntax_Base.ppname_default
                                      (Pulse_Syntax_Base.comp_res c1))
                                   (Pulse_Syntax_Naming.open_st_term_nv e2
                                      ((b.Pulse_Syntax_Base.binder_ppname),
                                        x)) c2 inter ty2))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     Pulse_Typing.T_Bind
                                       (g1, e1, e2, c1, c2, b, x, c3, uu___,
                                         (), uu___1, tot2))))) uu___)
            | uu___ ->
                Pulse_Typing_Env.fail g FStar_Pervasives_Native.None
                  "No common frame to extract..."
let rec (bring_frame_top :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          ((Pulse_Syntax_Base.comp,
             (unit, unit, unit) Pulse_Typing.st_typing,
             (unit, unit, unit) Pulse_Typing.st_equiv)
             FStar_Pervasives.dtuple3,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun t ->
               fun c ->
                 fun ty ->
                   match ty with
                   | Pulse_Typing.T_Frame (g1, e, c0, frame, tot_ty, ty') ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ ->
                                  FStar_Pervasives.Mkdtuple3
                                    (c, ty, (create_st_equiv g1 c c ())))))
                   | Pulse_Typing.T_Equiv
                       (uu___, uu___1, c1, uu___2, ty1, eq1) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (328))
                                        (Prims.of_int (56))
                                        (Prims.of_int (328))
                                        (Prims.of_int (84)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (328))
                                        (Prims.of_int (87))
                                        (Prims.of_int (336))
                                        (Prims.of_int (25)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> ()))
                               (fun uu___3 ->
                                  (fun eq11 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (329))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (329))
                                                   (Prims.of_int (31)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (336))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (336))
                                                   (Prims.of_int (25)))))
                                          (Obj.magic
                                             (bring_frame_top uu___ uu___1 c1
                                                ty1))
                                          (fun r ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  FStar_Pervasives.Mkdtuple3
                                                    ((FStar_Pervasives.__proj__Mkdtuple3__item___1
                                                        r),
                                                      (FStar_Pervasives.__proj__Mkdtuple3__item___2
                                                         r),
                                                      (create_st_equiv g
                                                         (FStar_Pervasives.__proj__Mkdtuple3__item___1
                                                            r) c ()))))))
                                    uu___3)))
                   | Pulse_Typing.T_Bind
                       (uu___, e1, e2, c1, c2, b, x, uu___1, ty1, uu___2,
                        ty2, bcomp2)
                       ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (339))
                                        (Prims.of_int (13))
                                        (Prims.of_int (339))
                                        (Prims.of_int (32)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (339))
                                        (Prims.of_int (35))
                                        (Prims.of_int (377))
                                        (Prims.of_int (47)))))
                               (Obj.magic (bring_frame_top uu___ e1 c1 ty1))
                               (fun uu___3 ->
                                  (fun r1 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (340))
                                                   (Prims.of_int (20))
                                                   (Prims.of_int (340))
                                                   (Prims.of_int (25)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (340))
                                                   (Prims.of_int (28))
                                                   (Prims.of_int (377))
                                                   (Prims.of_int (47)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                FStar_Pervasives.__proj__Mkdtuple3__item___1
                                                  r1))
                                          (fun uu___3 ->
                                             (fun c1' ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Par.fst"
                                                              (Prims.of_int (341))
                                                              (Prims.of_int (34))
                                                              (Prims.of_int (341))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Par.fst"
                                                              (Prims.of_int (341))
                                                              (Prims.of_int (42))
                                                              (Prims.of_int (377))
                                                              (Prims.of_int (47)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 ->
                                                           FStar_Pervasives.__proj__Mkdtuple3__item___2
                                                             r1))
                                                     (fun uu___3 ->
                                                        (fun ty11 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (32)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (47)))))
                                                                (Obj.magic
                                                                   (bring_frame_top
                                                                    (Pulse_Typing_Env.push_binding
                                                                    uu___ x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1))
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)) c2
                                                                    ty2))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun r2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.__proj__Mkdtuple3__item___1
                                                                    r2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun c2'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.__proj__Mkdtuple3__item___2
                                                                    r2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun ty21
                                                                    ->
                                                                    if
                                                                    (Pulse_Typing.uu___is_T_Frame
                                                                    g e1 c1'
                                                                    ty11) &&
                                                                    (Pulse_Typing.uu___is_T_Frame
                                                                    (Pulse_Typing_Env.push_binding
                                                                    uu___ x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1))
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)) c2'
                                                                    ty21)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match ty11
                                                                    with
                                                                    | 
                                                                    Pulse_Typing.T_Frame
                                                                    (uu___4,
                                                                    e11,
                                                                    c1'1, f1,
                                                                    totf1,
                                                                    ty12) ->
                                                                    (match ty21
                                                                    with
                                                                    | 
                                                                    Pulse_Typing.T_Frame
                                                                    (g1, e21,
                                                                    c2'1, f2,
                                                                    totf2,
                                                                    ty22) ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.add_frame
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1'1 c2'1)
                                                                    f1),
                                                                    (Pulse_Typing.T_Frame
                                                                    (g1,
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e11;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e21
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (t.Pulse_Syntax_Base.range2)
                                                                    },
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1'1 c2'1),
                                                                    f1, (),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g1, e11,
                                                                    e21,
                                                                    c1'1,
                                                                    c2'1,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    =
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1'1);
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    =
                                                                    (b.Pulse_Syntax_Base.binder_ppname)
                                                                    }, x,
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1'1 c2'1),
                                                                    ty12, (),
                                                                    ty22,
                                                                    bcomp2)))),
                                                                    (create_st_equiv
                                                                    g1
                                                                    (Pulse_Typing.add_frame
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1'1 c2'1)
                                                                    f1) c ()))))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Should not have happened...")))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                          uu___3))) uu___3)))
                                    uu___3)))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (Pulse_Typing_Env.fail g
                               FStar_Pervasives_Native.None
                               "No frame to bring to the top..."))) uu___3
            uu___2 uu___1 uu___
let (get_typing_deriv_and_frame :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          ((Pulse_Syntax_Base.comp,
             (unit, unit, unit) Pulse_Typing.st_typing,
             Pulse_Syntax_Base.vprop) FStar_Pervasives.dtuple3,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun c ->
        fun ty ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                     (Prims.of_int (384)) (Prims.of_int (10))
                     (Prims.of_int (384)) (Prims.of_int (28)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                     (Prims.of_int (384)) (Prims.of_int (31))
                     (Prims.of_int (394)) (Prims.of_int (3)))))
            (Obj.magic (bring_frame_top g t c ty))
            (fun uu___ ->
               (fun r ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                                (Prims.of_int (385)) (Prims.of_int (17))
                                (Prims.of_int (385)) (Prims.of_int (21)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                                (Prims.of_int (385)) (Prims.of_int (24))
                                (Prims.of_int (394)) (Prims.of_int (3)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             FStar_Pervasives.__proj__Mkdtuple3__item___1 r))
                       (fun uu___ ->
                          (fun c' ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Par.fst"
                                           (Prims.of_int (386))
                                           (Prims.of_int (30))
                                           (Prims.of_int (386))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Par.fst"
                                           (Prims.of_int (387))
                                           (Prims.of_int (2))
                                           (Prims.of_int (394))
                                           (Prims.of_int (3)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ ->
                                        FStar_Pervasives.__proj__Mkdtuple3__item___2
                                          r))
                                  (fun uu___ ->
                                     (fun ty' ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Par.fst"
                                                      (Prims.of_int (390))
                                                      (Prims.of_int (30))
                                                      (Prims.of_int (390))
                                                      (Prims.of_int (34)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Par.fst"
                                                      (Prims.of_int (391))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (393))
                                                      (Prims.of_int (59)))))
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___ ->
                                                   FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                     r))
                                             (fun uu___ ->
                                                (fun eq ->
                                                   match ty' with
                                                   | Pulse_Typing.T_Frame
                                                       (uu___, uu___1, c'',
                                                        f, tot, ty'1)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  FStar_Pervasives.Mkdtuple3
                                                                    (c'',
                                                                    ty'1, f))))
                                                   | uu___ ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (Pulse_Typing_Env.fail
                                                               g
                                                               FStar_Pervasives_Native.None
                                                               "Did not find a frame at the top...")))
                                                  uu___))) uu___))) uu___)))
                 uu___)
let (retypecheck_left_branch : unit -> Prims.bool) = fun uu___ -> true
let (check_par :
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
                           (Prims.of_int (410)) (Prims.of_int (12))
                           (Prims.of_int (410)) (Prims.of_int (46)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (410)) (Prims.of_int (49))
                           (Prims.of_int (455)) (Prims.of_int (50)))))
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
                                      (Prims.of_int (411))
                                      (Prims.of_int (86))
                                      (Prims.of_int (411))
                                      (Prims.of_int (92)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Par.fst"
                                      (Prims.of_int (410))
                                      (Prims.of_int (49))
                                      (Prims.of_int (455))
                                      (Prims.of_int (50)))))
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
                                                     (Prims.of_int (414))
                                                     (Prims.of_int (40))
                                                     (Prims.of_int (414))
                                                     (Prims.of_int (82)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Par.fst"
                                                     (Prims.of_int (411))
                                                     (Prims.of_int (95))
                                                     (Prims.of_int (455))
                                                     (Prims.of_int (50)))))
                                            (Obj.magic
                                               (check' allow_inst g1 eL pre
                                                  ()
                                                  FStar_Pervasives_Native.None))
                                            (fun uu___1 ->
                                               (fun uu___1 ->
                                                  match uu___1 with
                                                  | FStar_Pervasives.Mkdtuple3
                                                      (eL_t, cL_t,
                                                       eL_typing_t)
                                                      ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (43)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (50)))))
                                                           (Obj.magic
                                                              (simplify_st_typing
                                                                 g1 eL_t cL_t
                                                                 eL_typing_t))
                                                           (fun uu___2 ->
                                                              (fun ty ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (collect_frames
                                                                    g1 eL_t
                                                                    cL_t ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    compute_intersection_list
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    inter ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (50)))))
                                                                    (if
                                                                    retypecheck_left_branch
                                                                    ()
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (72)))))
                                                                    (Obj.magic
                                                                    (extract_common_frame
                                                                    g1 eL_t
                                                                    cL_t
                                                                    inter ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (get_typing_deriv_and_frame
                                                                    g1 eL_t
                                                                    cL_t
                                                                    uu___2))
                                                                    uu___2)))
                                                                    (fun r ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (eL_t,
                                                                    (FStar_Pervasives.__proj__Mkdtuple3__item___1
                                                                    r),
                                                                    (FStar_Pervasives.__proj__Mkdtuple3__item___2
                                                                    r),
                                                                    (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                                    r)))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (remove_from_vprop
                                                                    inter pre))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    new_preL
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    from_list_to_term
                                                                    preR.Pulse_Syntax_Base.range1
                                                                    inter))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    new_preR
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g1
                                                                    new_preL
                                                                    Pulse_Syntax_Base.tm_vprop))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (preL1,
                                                                    preL_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (39)))))
                                                                    (if
                                                                    Pulse_Syntax_Base.uu___is_Tm_Unknown
                                                                    postL.Pulse_Syntax_Base.t
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.intro_post_hint
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    postL))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___5)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    postL_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (435))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (435))
                                                                    (Prims.of_int (90)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g1 eL
                                                                    preL1 ()
                                                                    postL_hint))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eL1, cL,
                                                                    eL_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (eL1, cL,
                                                                    eL_typing,
                                                                    new_preR)))))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (eL1, cL,
                                                                    eL_typing,
                                                                    new_preR)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2))
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
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g1
                                                                    new_preR
                                                                    Pulse_Syntax_Base.tm_vprop))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (preR1,
                                                                    preR_typing)
                                                                    ->
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
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g1 eL1 cL
                                                                    eL_typing))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    cL_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (52)))))
                                                                    (if
                                                                    Pulse_Syntax_Base.uu___is_Tm_Unknown
                                                                    postR.Pulse_Syntax_Base.t
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (95)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.intro_post_hint
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    postR))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___6)))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    postR_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g1 eR
                                                                    preR1 ()
                                                                    postR_hint))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
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
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g1 eR1 cR
                                                                    eR_typing))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    cR_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_Par
                                                                    (g1, eL1,
                                                                    cL, eR1,
                                                                    cR, x,
                                                                    cL_typing,
                                                                    cR_typing,
                                                                    eL_typing,
                                                                    eR_typing)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.try_frame_pre
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
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
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
                                                                    }))
                                                                    uu___6
                                                                    post_hint))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (eR1.Pulse_Syntax_Base.range2))
                                                                    "par: cR is not stt"))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (eL1.Pulse_Syntax_Base.range2))
                                                                    "par: cL is not stt"))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                uu___2)))
                                                 uu___1))) uu___))) uu___)