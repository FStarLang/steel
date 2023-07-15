open Prims
let (print_term :
  Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Par.fst" (Prims.of_int (20))
               (Prims.of_int (12)) (Prims.of_int (20)) (Prims.of_int (30)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Par.fst" (Prims.of_int (20))
               (Prims.of_int (4)) (Prims.of_int (20)) (Prims.of_int (30)))))
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
                   (Prims.of_int (25)) (Prims.of_int (11))
                   (Prims.of_int (25)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                   (Prims.of_int (25)) (Prims.of_int (25))
                   (Prims.of_int (25)) (Prims.of_int (58)))))
          (Obj.magic (FStar_Tactics_V2_Builtins.print ", "))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (25)) (Prims.of_int (25))
                              (Prims.of_int (25)) (Prims.of_int (37)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (25)) (Prims.of_int (39))
                              (Prims.of_int (25)) (Prims.of_int (58)))))
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
                   (Prims.of_int (30)) (Prims.of_int (13))
                   (Prims.of_int (30)) (Prims.of_int (24)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                   (Prims.of_int (30)) (Prims.of_int (26))
                   (Prims.of_int (30)) (Prims.of_int (59)))))
          (Obj.magic (FStar_Tactics_V2_Builtins.print "["))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (30)) (Prims.of_int (26))
                              (Prims.of_int (30)) (Prims.of_int (38)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                              (Prims.of_int (30)) (Prims.of_int (40))
                              (Prims.of_int (30)) (Prims.of_int (59)))))
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
                       (Prims.of_int (48)) (Prims.of_int (2))
                       (Prims.of_int (48)) (Prims.of_int (33)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                       (Prims.of_int (39)) (Prims.of_int (4))
                       (Prims.of_int (48)) (Prims.of_int (33)))))
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
                                  (Prims.of_int (39)) (Prims.of_int (4))
                                  (Prims.of_int (48)) (Prims.of_int (33)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                                  (Prims.of_int (39)) (Prims.of_int (4))
                                  (Prims.of_int (48)) (Prims.of_int (33)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (39))
                                        (Prims.of_int (4))
                                        (Prims.of_int (48))
                                        (Prims.of_int (33)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (39))
                                        (Prims.of_int (4))
                                        (Prims.of_int (48))
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
                                              (Prims.of_int (33)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Par.fst"
                                              (Prims.of_int (39))
                                              (Prims.of_int (4))
                                              (Prims.of_int (48))
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
                                                         (Prims.of_int (39))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (48))
                                                         (Prims.of_int (33)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Par.fst"
                                                         (Prims.of_int (39))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (48))
                                                         (Prims.of_int (33)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Par.fst"
                                                               (Prims.of_int (39))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (48))
                                                               (Prims.of_int (33)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Par.fst"
                                                               (Prims.of_int (39))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (48))
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
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (48))
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
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (42))
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
      Pulse_Syntax_Base.comp_st ->
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
                                            (Prims.of_int (61))
                                            (Prims.of_int (6))
                                            (Prims.of_int (61))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Par.fst"
                                            (Prims.of_int (59))
                                            (Prims.of_int (6))
                                            (Prims.of_int (61))
                                            (Prims.of_int (47)))))
                                   (Obj.magic
                                      (st_typing_to_string'
                                         (Pulse_Typing_Env.push_binding g1 x
                                            Pulse_Syntax_Base.ppname_default
                                            (Pulse_Syntax_Base.comp_res c1))
                                         (Pulse_Syntax_Naming.open_st_term_nv
                                            e2
                                            ((b.Pulse_Syntax_Base.binder_ppname),
                                              x)) c2 (indent level) ty2))
                                   (fun uu___2 ->
                                      (fun uu___2 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (59))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (61))
                                                       (Prims.of_int (47)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (59))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (61))
                                                       (Prims.of_int (47)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Par.fst"
                                                             (Prims.of_int (60))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (60))
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
                                                    (fun uu___3 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___4 ->
                                                            fun x1 ->
                                                              Prims.strcat
                                                                (Prims.strcat
                                                                   "T_Bind \n ("
                                                                   (Prims.strcat
                                                                    uu___3
                                                                    "); \n ("))
                                                                (Prims.strcat
                                                                   x1 ")")))))
                                              (fun uu___3 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___4 ->
                                                      uu___3 uu___2))))
                                        uu___2)))
                       | Pulse_Typing.T_TotBind
                           (g1, e1, e2, t1, c2, x, uu___, ty') ->
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
                                            (Prims.of_int (69))
                                            (Prims.of_int (6))
                                            (Prims.of_int (69))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Par.fst"
                                            (Prims.of_int (66))
                                            (Prims.of_int (6))
                                            (Prims.of_int (69))
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
                                                       (Prims.of_int (66))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (69))
                                                       (Prims.of_int (47)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Par.fst"
                                                       (Prims.of_int (66))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (69))
                                                       (Prims.of_int (47)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Par.fst"
                                                             (Prims.of_int (66))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (69))
                                                             (Prims.of_int (47)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Par.fst"
                                                             (Prims.of_int (66))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (69))
                                                             (Prims.of_int (47)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Par.fst"
                                                                   (Prims.of_int (67))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (67))
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
                                            (Prims.of_int (75))
                                            (Prims.of_int (6))
                                            (Prims.of_int (75))
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
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun g -> fun t -> fun c -> fun ty -> st_typing_to_string' g t c "" ty
let (create_st_equiv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      Pulse_Syntax_Base.comp_st -> (unit, unit, unit) Pulse_Typing.st_equiv)
  =
  fun g ->
    fun c ->
      fun c' ->
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
                let st_eq = create_st_equiv g1 c' c in
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
let rec (collapse_equiv :
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
                   match ty with
                   | Pulse_Typing.T_Equiv
                       (uu___, uu___1, c', uu___2, Pulse_Typing.T_Equiv
                        (uu___3, uu___4, c'', uu___5, ty', eq'), eq)
                       ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (117))
                                        (Prims.of_int (32))
                                        (Prims.of_int (117))
                                        (Prims.of_int (55)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (118))
                                        (Prims.of_int (2))
                                        (Prims.of_int (118))
                                        (Prims.of_int (46)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___6 -> create_st_equiv g c'' c))
                               (fun uu___6 ->
                                  (fun st_eq ->
                                     Obj.magic
                                       (collapse_equiv g e c
                                          (Pulse_Typing.T_Equiv
                                             (g, e, c'', c, ty', st_eq))))
                                    uu___6)))
                   | Pulse_Typing.T_Equiv
                       (uu___, uu___1, c', uu___2, ty', eq) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (119))
                                        (Prims.of_int (48))
                                        (Prims.of_int (119))
                                        (Prims.of_int (68)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (119))
                                        (Prims.of_int (31))
                                        (Prims.of_int (119))
                                        (Prims.of_int (71)))))
                               (Obj.magic
                                  (collapse_equiv uu___ uu___1 c' ty'))
                               (fun uu___3 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___4 ->
                                       Pulse_Typing.T_Equiv
                                         (g, e, c', c, uu___3, eq)))))
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
                                        (Prims.of_int (121))
                                        (Prims.of_int (29))
                                        (Prims.of_int (121))
                                        (Prims.of_int (49)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (121))
                                        (Prims.of_int (2))
                                        (Prims.of_int (121))
                                        (Prims.of_int (80)))))
                               (Obj.magic (collapse_equiv g1 e1 c1 ty1))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (121))
                                                   (Prims.of_int (55))
                                                   (Prims.of_int (121))
                                                   (Prims.of_int (75)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (121))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (121))
                                                   (Prims.of_int (80)))))
                                          (Obj.magic
                                             (collapse_equiv
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
                                                  Pulse_Typing.T_Bind
                                                    (g1, e1, e2, c1, c2, b,
                                                      x, c3, uu___, (),
                                                      uu___1, tot2))))) uu___)))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> ty)))) uu___3 uu___2 uu___1
            uu___
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
                                        (Prims.of_int (129))
                                        (Prims.of_int (52))
                                        (Prims.of_int (129))
                                        (Prims.of_int (70)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (129))
                                        (Prims.of_int (52))
                                        (Prims.of_int (129))
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
                                                   (Prims.of_int (129))
                                                   (Prims.of_int (73))
                                                   (Prims.of_int (129))
                                                   (Prims.of_int (91)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (129))
                                                   (Prims.of_int (52))
                                                   (Prims.of_int (129))
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
  fun g ->
    fun e ->
      fun c ->
        fun ty ->
          collapse_equiv g e c (replace_frame_emp_with_equiv g e c ty)
let rec (is_host_term_in_vprop :
  Pulse_Syntax_Base.host_term -> Pulse_Syntax_Base.term -> Prims.bool) =
  fun ft ->
    fun t ->
      match t.Pulse_Syntax_Base.t with
      | Pulse_Syntax_Base.Tm_FStar ht ->
          FStar_Reflection_V1_Builtins.term_eq ft ht
      | Pulse_Syntax_Base.Tm_Star (l, r) ->
          (is_host_term_in_vprop ft l) || (is_host_term_in_vprop ft r)
      | uu___ -> false
let rec (compute_intersection :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.host_term Prims.list)
  =
  fun t1 ->
    fun t2 ->
      match t1.Pulse_Syntax_Base.t with
      | Pulse_Syntax_Base.Tm_FStar ft ->
          if is_host_term_in_vprop ft t2 then [ft] else []
      | Pulse_Syntax_Base.Tm_Star (l, r) ->
          FStar_List_Tot_Base.op_At (compute_intersection l t2)
            (compute_intersection r t2)
      | uu___ -> []
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
                            (Prims.of_int (152)) (Prims.of_int (12))
                            (Prims.of_int (152)) (Prims.of_int (30)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                            (Prims.of_int (152)) (Prims.of_int (12))
                            (Prims.of_int (152)) (Prims.of_int (70)))))
                   (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string t))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Par.fst"
                                       (Prims.of_int (152))
                                       (Prims.of_int (33))
                                       (Prims.of_int (152))
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
                                             (Prims.of_int (152))
                                             (Prims.of_int (40))
                                             (Prims.of_int (152))
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
                           (Prims.of_int (165)) (Prims.of_int (12))
                           (Prims.of_int (165)) (Prims.of_int (46)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (165)) (Prims.of_int (49))
                           (Prims.of_int (241)) (Prims.of_int (4)))))
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
                                      (Prims.of_int (167))
                                      (Prims.of_int (52))
                                      (Prims.of_int (167))
                                      (Prims.of_int (58)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Par.fst"
                                      (Prims.of_int (165))
                                      (Prims.of_int (49))
                                      (Prims.of_int (241)) (Prims.of_int (4)))))
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
                                                     (Prims.of_int (169))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (169))
                                                     (Prims.of_int (94)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Par.fst"
                                                     (Prims.of_int (169))
                                                     (Prims.of_int (97))
                                                     (Prims.of_int (241))
                                                     (Prims.of_int (4)))))
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
                                                                (Prims.of_int (169))
                                                                (Prims.of_int (63))
                                                                (Prims.of_int (169))
                                                                (Prims.of_int (93)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Par.fst"
                                                                (Prims.of_int (169))
                                                                (Prims.of_int (58))
                                                                (Prims.of_int (169))
                                                                (Prims.of_int (93)))))
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
                                                                (Prims.of_int (171))
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (171))
                                                                (Prims.of_int (86)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Par.fst"
                                                                (Prims.of_int (169))
                                                                (Prims.of_int (97))
                                                                (Prims.of_int (241))
                                                                (Prims.of_int (4)))))
                                                       (Obj.magic
                                                          (check' allow_inst
                                                             g1 eR pre ()
                                                             postL_hint))
                                                       (fun uu___1 ->
                                                          (fun uu___1 ->
                                                             match uu___1
                                                             with
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
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    "Typechecked left branch with whole context!"))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (simplify_st_typing
                                                                    g1 eL_t
                                                                    cL_t
                                                                    eL_typing_t))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (collect_frames
                                                                    g1 eL_t
                                                                    cL_t ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun l ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (54)))))
                                                                    (match l
                                                                    with
                                                                    | 
                                                                    t1::t2::[]
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    "Computed intersection: "))
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
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    (list_of_FStar_term_to_string
                                                                    (compute_intersection
                                                                    t1 t2)))
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
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    "End of intersection"))
                                                                    uu___4)))
                                                                    uu___3))
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    "Does not have two elements..."))
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
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (print_list_terms
                                                                    l))
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
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (st_typing_to_string
                                                                    g1 eL_t
                                                                    cL_t ty))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___5))
                                                                    uu___5)))
                                                                    uu___4)))
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
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (3)))))
                                                                    (if
                                                                    (Pulse_Syntax_Base.uu___is_Tm_STApp
                                                                    eL.Pulse_Syntax_Base.term1)
                                                                    &&
                                                                    (Pulse_Syntax_Base.uu___is_Tm_Unknown
                                                                    preL.Pulse_Syntax_Base.t)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    eL.Pulse_Syntax_Base.term1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term
                                                                    g1 head))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (head1,
                                                                    ty_head,
                                                                    dhead) ->
                                                                    (match 
                                                                    Pulse_Syntax_Pure.is_arrow
                                                                    ty_head
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ({
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = formal;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;_},
                                                                    bqual,
                                                                    comp_typ)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    qual =
                                                                    bqual
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g1 arg
                                                                    formal))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (arg1,
                                                                    darg) ->
                                                                    (match comp_typ
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_ST
                                                                    res ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    pre_app
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (61)))))
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
                                                                    pre))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Trying to frame in parallel block, context: "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    " and pre: "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8
                                                                    uu___7))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___7))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Framing.check_frameable
                                                                    g pre ()
                                                                    pre_app))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    failure
                                                                    ->
                                                                    (preL,
                                                                    preR)
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    frame_t
                                                                    ->
                                                                    (pre_app,
                                                                    (FStar_Pervasives.__proj__Mkdtuple3__item___1
                                                                    frame_t))))))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___7,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    pre_app
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (61)))))
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
                                                                    pre))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Trying to frame in parallel block, context: "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    " and pre: "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    uu___8))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___8))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Framing.check_frameable
                                                                    g pre ()
                                                                    pre_app))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    failure
                                                                    ->
                                                                    (preL,
                                                                    preR)
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    frame_t
                                                                    ->
                                                                    (pre_app,
                                                                    (FStar_Pervasives.__proj__Mkdtuple3__item___1
                                                                    frame_t))))))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (uu___7,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    pre_app
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (61)))))
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
                                                                    pre))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Trying to frame in parallel block, context: "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    " and pre: "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    uu___8))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___8))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Framing.check_frameable
                                                                    g pre ()
                                                                    pre_app))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    failure
                                                                    ->
                                                                    (preL,
                                                                    preR)
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    frame_t
                                                                    ->
                                                                    (pre_app,
                                                                    (FStar_Pervasives.__proj__Mkdtuple3__item___1
                                                                    frame_t))))))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_Tot
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    (preL,
                                                                    preR))))))
                                                                    uu___6))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (preL,
                                                                    preR)))))
                                                                    | 
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (preL,
                                                                    preR))))))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (preL,
                                                                    preR)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (new_preL,
                                                                    new_preR)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4))
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
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g1
                                                                    new_preL
                                                                    Pulse_Syntax_Base.tm_vprop))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
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
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g1 eL
                                                                    preL1 ()
                                                                    postL_hint))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eL1, cL,
                                                                    eL_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g1
                                                                    new_preR
                                                                    Pulse_Syntax_Base.tm_vprop))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
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
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g1 eL1 cL
                                                                    eL_typing))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    cL_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (52)))))
                                                                    (if
                                                                    Pulse_Syntax_Base.uu___is_Tm_Unknown
                                                                    postR.Pulse_Syntax_Base.t
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (95)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.intro_post_hint
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    postR))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___10)))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    postR_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g1 eR
                                                                    preR1 ()
                                                                    postR_hint))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
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
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g1 eR1 cR
                                                                    eR_typing))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    cR_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Typing.T_Par
                                                                    (g1, eL1,
                                                                    cL, eR1,
                                                                    cR, x,
                                                                    cL_typing,
                                                                    cR_typing,
                                                                    eL_typing,
                                                                    eR_typing)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (238))
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
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
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
                                                                    uu___10
                                                                    post_hint))
                                                                    uu___10)))
                                                                    uu___10)))
                                                                    uu___10)))
                                                                    uu___10))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (eR1.Pulse_Syntax_Base.range2))
                                                                    "par: cR is not stt"))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (eL1.Pulse_Syntax_Base.range2))
                                                                    "par: cL is not stt"))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                            uu___1))) uu___1)))
                                  uu___))) uu___)