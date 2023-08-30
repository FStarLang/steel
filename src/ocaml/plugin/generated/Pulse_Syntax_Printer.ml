open Prims
let (tot_or_ghost_to_string :
  FStar_TypeChecker_Core.tot_or_ghost -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Core.E_Total -> "total"
    | FStar_TypeChecker_Core.E_Ghost -> "ghost"
let (name_to_string : FStar_Reflection_Types.name -> Prims.string) =
  fun f -> FStar_String.concat "." f
let (dbg_printing : Prims.bool) = true
let rec (universe_to_string :
  Prims.nat -> Pulse_Syntax_Base.universe -> Prims.string) =
  fun n ->
    fun u ->
      match FStar_Reflection_V2_Builtins.inspect_universe u with
      | FStar_Reflection_V2_Data.Uv_Unk -> "_"
      | FStar_Reflection_V2_Data.Uv_Zero ->
          Prims.strcat "" (Prims.strcat (Prims.string_of_int n) "")
      | FStar_Reflection_V2_Data.Uv_Succ u1 ->
          universe_to_string (n + Prims.int_one) u1
      | FStar_Reflection_V2_Data.Uv_BVar x ->
          if n = Prims.int_zero
          then Prims.strcat "" (Prims.strcat (Prims.string_of_int x) "")
          else
            Prims.strcat
              (Prims.strcat "(" (Prims.strcat (Prims.string_of_int x) " + "))
              (Prims.strcat (Prims.string_of_int n) ")")
      | FStar_Reflection_V2_Data.Uv_Max us ->
          let r = "(max _)" in
          if n = Prims.int_zero
          then r
          else
            Prims.strcat (Prims.strcat "" (Prims.strcat r " + "))
              (Prims.strcat (Prims.string_of_int n) "")
      | uu___ -> "<univ>"
let (univ_to_string : Pulse_Syntax_Base.universe -> Prims.string) =
  fun u ->
    Prims.strcat "u#" (Prims.strcat (universe_to_string Prims.int_zero u) "")
let (qual_to_string :
  Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Implicit) -> "#"
let (indent : Prims.string -> Prims.string) =
  fun level -> Prims.strcat level "\t"
let rec (term_to_string' :
  Prims.string ->
    Pulse_Syntax_Base.term ->
      (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun level ->
         fun t ->
           match t.Pulse_Syntax_Base.t with
           | Pulse_Syntax_Base.Tm_Emp ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "emp")))
           | Pulse_Syntax_Base.Tm_Inv p ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (55)) (Prims.of_int (8))
                                (Prims.of_int (55)) (Prims.of_int (42)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "prims.fst"
                                (Prims.of_int (590)) (Prims.of_int (19))
                                (Prims.of_int (590)) (Prims.of_int (31)))))
                       (Obj.magic (term_to_string' (indent level) p))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               Prims.strcat
                                 (Prims.strcat "inv (\n"
                                    (Prims.strcat (indent level) ""))
                                 (Prims.strcat uu___ ")")))))
           | Pulse_Syntax_Base.Tm_Pure p ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (60)) (Prims.of_int (8))
                                (Prims.of_int (60)) (Prims.of_int (42)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "prims.fst"
                                (Prims.of_int (590)) (Prims.of_int (19))
                                (Prims.of_int (590)) (Prims.of_int (31)))))
                       (Obj.magic (term_to_string' (indent level) p))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               Prims.strcat
                                 (Prims.strcat "pure (\n"
                                    (Prims.strcat (indent level) ""))
                                 (Prims.strcat uu___ ")")))))
           | Pulse_Syntax_Base.Tm_Star (p1, p2) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (66)) (Prims.of_int (8))
                                (Prims.of_int (66)) (Prims.of_int (34)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (63)) (Prims.of_int (6))
                                (Prims.of_int (66)) (Prims.of_int (34)))))
                       (Obj.magic (term_to_string' level p2))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (63))
                                           (Prims.of_int (6))
                                           (Prims.of_int (66))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (63))
                                           (Prims.of_int (6))
                                           (Prims.of_int (66))
                                           (Prims.of_int (34)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (63))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (66))
                                                 (Prims.of_int (34)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (63))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (66))
                                                 (Prims.of_int (34)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (64))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (64))
                                                       (Prims.of_int (34)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Printf.fst"
                                                       (Prims.of_int (121))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (123))
                                                       (Prims.of_int (44)))))
                                              (Obj.magic
                                                 (term_to_string' level p1))
                                              (fun uu___1 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      fun x ->
                                                        fun x1 ->
                                                          Prims.strcat
                                                            (Prims.strcat
                                                               (Prims.strcat
                                                                  ""
                                                                  (Prims.strcat
                                                                    uu___1
                                                                    " ** \n"))
                                                               (Prims.strcat
                                                                  x ""))
                                                            (Prims.strcat x1
                                                               "")))))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 -> uu___1 level))))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> uu___1 uu___)))) uu___)))
           | Pulse_Syntax_Base.Tm_ExistsSL (uu___, b, body) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (73)) (Prims.of_int (14))
                                (Prims.of_int (73)) (Prims.of_int (51)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (69)) (Prims.of_int (6))
                                (Prims.of_int (73)) (Prims.of_int (51)))))
                       (Obj.magic (term_to_string' (indent level) body))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (69))
                                           (Prims.of_int (6))
                                           (Prims.of_int (73))
                                           (Prims.of_int (51)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (69))
                                           (Prims.of_int (6))
                                           (Prims.of_int (73))
                                           (Prims.of_int (51)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (69))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (73))
                                                 (Prims.of_int (51)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (69))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (73))
                                                 (Prims.of_int (51)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (71))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (71))
                                                       (Prims.of_int (58)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (69))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (73))
                                                       (Prims.of_int (51)))))
                                              (Obj.magic
                                                 (term_to_string'
                                                    (indent level)
                                                    b.Pulse_Syntax_Base.binder_ty))
                                              (fun uu___2 ->
                                                 (fun uu___2 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Syntax.Printer.fst"
                                                                  (Prims.of_int (69))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (73))
                                                                  (Prims.of_int (51)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Syntax.Printer.fst"
                                                                  (Prims.of_int (69))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (73))
                                                                  (Prims.of_int (51)))))
                                                         (Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (45)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Unseal.unseal
                                                                    (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name))
                                                               (fun uu___3 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "(exists ("
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    ":"))
                                                                    (Prims.strcat
                                                                    x ").\n"))
                                                                    (Prims.strcat
                                                                    x1 ""))
                                                                    (Prims.strcat
                                                                    x2 ")")))))
                                                         (fun uu___3 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___4 ->
                                                                 uu___3
                                                                   uu___2))))
                                                   uu___2)))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 -> uu___2 level))))
                                  (fun uu___2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 -> uu___2 uu___1))))
                            uu___1)))
           | Pulse_Syntax_Base.Tm_ForallSL (u, b, body) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (80)) (Prims.of_int (14))
                                (Prims.of_int (80)) (Prims.of_int (51)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (76)) (Prims.of_int (6))
                                (Prims.of_int (80)) (Prims.of_int (51)))))
                       (Obj.magic (term_to_string' (indent level) body))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (76))
                                           (Prims.of_int (6))
                                           (Prims.of_int (80))
                                           (Prims.of_int (51)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (76))
                                           (Prims.of_int (6))
                                           (Prims.of_int (80))
                                           (Prims.of_int (51)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (76))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (80))
                                                 (Prims.of_int (51)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (76))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (80))
                                                 (Prims.of_int (51)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (78))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (78))
                                                       (Prims.of_int (58)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (76))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (80))
                                                       (Prims.of_int (51)))))
                                              (Obj.magic
                                                 (term_to_string'
                                                    (indent level)
                                                    b.Pulse_Syntax_Base.binder_ty))
                                              (fun uu___1 ->
                                                 (fun uu___1 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Syntax.Printer.fst"
                                                                  (Prims.of_int (76))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (80))
                                                                  (Prims.of_int (51)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Syntax.Printer.fst"
                                                                  (Prims.of_int (76))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (80))
                                                                  (Prims.of_int (51)))))
                                                         (Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (45)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Unseal.unseal
                                                                    (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name))
                                                               (fun uu___2 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "(forall ("
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    ":"))
                                                                    (Prims.strcat
                                                                    x ").\n"))
                                                                    (Prims.strcat
                                                                    x1 ""))
                                                                    (Prims.strcat
                                                                    x2 ")")))))
                                                         (fun uu___2 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___3 ->
                                                                 uu___2
                                                                   uu___1))))
                                                   uu___1)))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 -> uu___1 level))))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> uu___1 uu___)))) uu___)))
           | Pulse_Syntax_Base.Tm_VProp ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "vprop")))
           | Pulse_Syntax_Base.Tm_Inames ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> "inames")))
           | Pulse_Syntax_Base.Tm_EmpInames ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> "emp_inames")))
           | Pulse_Syntax_Base.Tm_Unknown ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "_")))
           | Pulse_Syntax_Base.Tm_FStar t1 ->
               Obj.magic
                 (Obj.repr (FStar_Tactics_V2_Builtins.term_to_string t1)))
        uu___1 uu___
let (term_to_string :
  Pulse_Syntax_Base.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> term_to_string' "" t
let (binder_to_string :
  Pulse_Syntax_Base.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (94)) (Prims.of_int (12)) (Prims.of_int (94))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (92)) (Prims.of_int (4)) (Prims.of_int (94))
               (Prims.of_int (40)))))
      (Obj.magic (term_to_string b.Pulse_Syntax_Base.binder_ty))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (92)) (Prims.of_int (4))
                          (Prims.of_int (94)) (Prims.of_int (40)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (92)) (Prims.of_int (4))
                          (Prims.of_int (94)) (Prims.of_int (40)))))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (93)) (Prims.of_int (12))
                                (Prims.of_int (93)) (Prims.of_int (43)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Printf.fst"
                                (Prims.of_int (121)) (Prims.of_int (8))
                                (Prims.of_int (123)) (Prims.of_int (44)))))
                       (Obj.magic
                          (FStar_Tactics_Unseal.unseal
                             (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               fun x ->
                                 Prims.strcat
                                   (Prims.strcat "" (Prims.strcat uu___1 ":"))
                                   (Prims.strcat x "")))))
                 (fun uu___1 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 -> uu___1 uu___)))) uu___)
let (ctag_to_string : Pulse_Syntax_Base.ctag -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Pulse_Syntax_Base.STT -> "ST"
    | Pulse_Syntax_Base.STT_Atomic -> "STAtomic"
    | Pulse_Syntax_Base.STT_Ghost -> "STGhost"
let (comp_to_string :
  Pulse_Syntax_Base.comp ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun c ->
    match c with
    | Pulse_Syntax_Base.C_Tot t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (105)) (Prims.of_int (23))
                   (Prims.of_int (105)) (Prims.of_int (41)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                   (Prims.of_int (19)) (Prims.of_int (590))
                   (Prims.of_int (31))))) (Obj.magic (term_to_string t))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> Prims.strcat "Tot " (Prims.strcat uu___ "")))
    | Pulse_Syntax_Base.C_ST s ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (111)) (Prims.of_int (14))
                   (Prims.of_int (111)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (108)) (Prims.of_int (6))
                   (Prims.of_int (111)) (Prims.of_int (37)))))
          (Obj.magic (term_to_string s.Pulse_Syntax_Base.post))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (108)) (Prims.of_int (6))
                              (Prims.of_int (111)) (Prims.of_int (37)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (108)) (Prims.of_int (6))
                              (Prims.of_int (111)) (Prims.of_int (37)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (110)) (Prims.of_int (14))
                                    (Prims.of_int (110)) (Prims.of_int (36)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (108)) (Prims.of_int (6))
                                    (Prims.of_int (111)) (Prims.of_int (37)))))
                           (Obj.magic
                              (term_to_string s.Pulse_Syntax_Base.pre))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (108))
                                               (Prims.of_int (6))
                                               (Prims.of_int (111))
                                               (Prims.of_int (37)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (108))
                                               (Prims.of_int (6))
                                               (Prims.of_int (111))
                                               (Prims.of_int (37)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (109))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (109))
                                                     (Prims.of_int (36)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Printf.fst"
                                                     (Prims.of_int (121))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (123))
                                                     (Prims.of_int (44)))))
                                            (Obj.magic
                                               (term_to_string
                                                  s.Pulse_Syntax_Base.res))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    fun x ->
                                                      fun x1 ->
                                                        Prims.strcat
                                                          (Prims.strcat
                                                             (Prims.strcat
                                                                "stt "
                                                                (Prims.strcat
                                                                   uu___2
                                                                   " (requires\n"))
                                                             (Prims.strcat x
                                                                ") (ensures\n"))
                                                          (Prims.strcat x1
                                                             ")")))))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> uu___2 uu___1))))
                                uu___1)))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.C_STAtomic (inames, s) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (118)) (Prims.of_int (14))
                   (Prims.of_int (118)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (114)) (Prims.of_int (6))
                   (Prims.of_int (118)) (Prims.of_int (37)))))
          (Obj.magic (term_to_string s.Pulse_Syntax_Base.post))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (114)) (Prims.of_int (6))
                              (Prims.of_int (118)) (Prims.of_int (37)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (114)) (Prims.of_int (6))
                              (Prims.of_int (118)) (Prims.of_int (37)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (117)) (Prims.of_int (14))
                                    (Prims.of_int (117)) (Prims.of_int (36)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (114)) (Prims.of_int (6))
                                    (Prims.of_int (118)) (Prims.of_int (37)))))
                           (Obj.magic
                              (term_to_string s.Pulse_Syntax_Base.pre))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (114))
                                               (Prims.of_int (6))
                                               (Prims.of_int (118))
                                               (Prims.of_int (37)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (114))
                                               (Prims.of_int (6))
                                               (Prims.of_int (118))
                                               (Prims.of_int (37)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (116))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (116))
                                                     (Prims.of_int (36)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (114))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (118))
                                                     (Prims.of_int (37)))))
                                            (Obj.magic
                                               (term_to_string
                                                  s.Pulse_Syntax_Base.res))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (114))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (118))
                                                                (Prims.of_int (37)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (114))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (118))
                                                                (Prims.of_int (37)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (37)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                             (Obj.magic
                                                                (term_to_string
                                                                   inames))
                                                             (fun uu___3 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "stt_atomic "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " (requires\n"))
                                                                    (Prims.strcat
                                                                    x1
                                                                    ") (ensures\n"))
                                                                    (Prims.strcat
                                                                    x2 ")")))))
                                                       (fun uu___3 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               uu___3 uu___2))))
                                                 uu___2)))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> uu___2 uu___1))))
                                uu___1)))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.C_STGhost (inames, s) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (125)) (Prims.of_int (14))
                   (Prims.of_int (125)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (121)) (Prims.of_int (6))
                   (Prims.of_int (125)) (Prims.of_int (37)))))
          (Obj.magic (term_to_string s.Pulse_Syntax_Base.post))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (121)) (Prims.of_int (6))
                              (Prims.of_int (125)) (Prims.of_int (37)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (121)) (Prims.of_int (6))
                              (Prims.of_int (125)) (Prims.of_int (37)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (124)) (Prims.of_int (14))
                                    (Prims.of_int (124)) (Prims.of_int (36)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (121)) (Prims.of_int (6))
                                    (Prims.of_int (125)) (Prims.of_int (37)))))
                           (Obj.magic
                              (term_to_string s.Pulse_Syntax_Base.pre))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (121))
                                               (Prims.of_int (6))
                                               (Prims.of_int (125))
                                               (Prims.of_int (37)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (121))
                                               (Prims.of_int (6))
                                               (Prims.of_int (125))
                                               (Prims.of_int (37)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (123))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (123))
                                                     (Prims.of_int (36)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (121))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (125))
                                                     (Prims.of_int (37)))))
                                            (Obj.magic
                                               (term_to_string
                                                  s.Pulse_Syntax_Base.res))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (121))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (125))
                                                                (Prims.of_int (37)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (121))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (125))
                                                                (Prims.of_int (37)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (37)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                             (Obj.magic
                                                                (term_to_string
                                                                   inames))
                                                             (fun uu___3 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "stt_atomic "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " (requires\n"))
                                                                    (Prims.strcat
                                                                    x1
                                                                    ") (ensures\n"))
                                                                    (Prims.strcat
                                                                    x2 ")")))))
                                                       (fun uu___3 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               uu___3 uu___2))))
                                                 uu___2)))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> uu___2 uu___1))))
                                uu___1)))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
let (term_opt_to_string :
  Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match t with
       | FStar_Pervasives_Native.None ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | FStar_Pervasives_Native.Some t1 ->
           Obj.magic (Obj.repr (term_to_string t1))) uu___
let (term_list_to_string :
  Prims.string ->
    Pulse_Syntax_Base.term Prims.list ->
      (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun sep ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                 (Prims.of_int (135)) (Prims.of_int (22))
                 (Prims.of_int (135)) (Prims.of_int (46)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                 (Prims.of_int (135)) (Prims.of_int (4)) (Prims.of_int (135))
                 (Prims.of_int (46)))))
        (Obj.magic (FStar_Tactics_Util.map term_to_string t))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStar_String.concat sep uu___))
let rec (st_term_to_string' :
  Prims.string ->
    Pulse_Syntax_Base.st_term ->
      (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun level ->
    fun t ->
      match t.Pulse_Syntax_Base.term1 with
      | Pulse_Syntax_Base.Tm_Return
          { Pulse_Syntax_Base.ctag = ctag;
            Pulse_Syntax_Base.insert_eq = insert_eq;
            Pulse_Syntax_Base.term = term;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (147)) (Prims.of_int (8))
                     (Prims.of_int (147)) (Prims.of_int (29)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                     (Prims.of_int (19)) (Prims.of_int (590))
                     (Prims.of_int (31))))) (Obj.magic (term_to_string term))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    Prims.strcat
                      (Prims.strcat
                         (Prims.strcat "return_"
                            (Prims.strcat
                               (match ctag with
                                | Pulse_Syntax_Base.STT -> "stt"
                                | Pulse_Syntax_Base.STT_Atomic ->
                                    "stt_atomic"
                                | Pulse_Syntax_Base.STT_Ghost -> "stt_ghost")
                               ""))
                         (Prims.strcat (if insert_eq then "" else "_noeq")
                            " ")) (Prims.strcat uu___ "")))
      | Pulse_Syntax_Base.Tm_STApp
          { Pulse_Syntax_Base.head = head;
            Pulse_Syntax_Base.arg_qual = arg_qual;
            Pulse_Syntax_Base.arg = arg;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (154)) (Prims.of_int (8))
                     (Prims.of_int (154)) (Prims.of_int (28)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (150)) (Prims.of_int (6))
                     (Prims.of_int (154)) (Prims.of_int (28)))))
            (Obj.magic (term_to_string arg))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (150)) (Prims.of_int (6))
                                (Prims.of_int (154)) (Prims.of_int (28)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (150)) (Prims.of_int (6))
                                (Prims.of_int (154)) (Prims.of_int (28)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (150)) (Prims.of_int (6))
                                      (Prims.of_int (154))
                                      (Prims.of_int (28)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (150)) (Prims.of_int (6))
                                      (Prims.of_int (154))
                                      (Prims.of_int (28)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (152))
                                            (Prims.of_int (8))
                                            (Prims.of_int (152))
                                            (Prims.of_int (29)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Printf.fst"
                                            (Prims.of_int (121))
                                            (Prims.of_int (8))
                                            (Prims.of_int (123))
                                            (Prims.of_int (44)))))
                                   (Obj.magic (term_to_string head))
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           fun x ->
                                             fun x1 ->
                                               Prims.strcat
                                                 (Prims.strcat
                                                    (Prims.strcat
                                                       (Prims.strcat "("
                                                          (Prims.strcat
                                                             (if dbg_printing
                                                              then "<stapp>"
                                                              else "") ""))
                                                       (Prims.strcat uu___1
                                                          " "))
                                                    (Prims.strcat x ""))
                                                 (Prims.strcat x1 ")")))))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     uu___1 (qual_to_string arg_qual)))))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> uu___1 uu___)))) uu___)
      | Pulse_Syntax_Base.Tm_Bind
          { Pulse_Syntax_Base.binder = binder;
            Pulse_Syntax_Base.head1 = head; Pulse_Syntax_Base.body1 = body;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (167)) (Prims.of_int (10))
                     (Prims.of_int (167)) (Prims.of_int (41)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (163)) (Prims.of_int (8))
                     (Prims.of_int (167)) (Prims.of_int (41)))))
            (Obj.magic (st_term_to_string' level body))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (163)) (Prims.of_int (8))
                                (Prims.of_int (167)) (Prims.of_int (41)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (163)) (Prims.of_int (8))
                                (Prims.of_int (167)) (Prims.of_int (41)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (163)) (Prims.of_int (8))
                                      (Prims.of_int (167))
                                      (Prims.of_int (41)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (163)) (Prims.of_int (8))
                                      (Prims.of_int (167))
                                      (Prims.of_int (41)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (165))
                                            (Prims.of_int (10))
                                            (Prims.of_int (165))
                                            (Prims.of_int (41)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (163))
                                            (Prims.of_int (8))
                                            (Prims.of_int (167))
                                            (Prims.of_int (41)))))
                                   (Obj.magic (st_term_to_string' level head))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (163))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (167))
                                                       (Prims.of_int (41)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (163))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (167))
                                                       (Prims.of_int (41)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (164))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (164))
                                                             (Prims.of_int (35)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Printf.fst"
                                                             (Prims.of_int (121))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (123))
                                                             (Prims.of_int (44)))))
                                                    (Obj.magic
                                                       (binder_to_string
                                                          binder))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            fun x ->
                                                              fun x1 ->
                                                                fun x2 ->
                                                                  Prims.strcat
                                                                    (
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "let "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " = "))
                                                                    (Prims.strcat
                                                                    x ";\n"))
                                                                    (Prims.strcat
                                                                    x1 ""))
                                                                    (
                                                                    Prims.strcat
                                                                    x2 "")))))
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
      | Pulse_Syntax_Base.Tm_TotBind
          { Pulse_Syntax_Base.binder1 = binder;
            Pulse_Syntax_Base.head2 = head; Pulse_Syntax_Base.body2 = body;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (175)) (Prims.of_int (8))
                     (Prims.of_int (175)) (Prims.of_int (39)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (171)) (Prims.of_int (6))
                     (Prims.of_int (175)) (Prims.of_int (39)))))
            (Obj.magic (st_term_to_string' level body))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (171)) (Prims.of_int (6))
                                (Prims.of_int (175)) (Prims.of_int (39)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (171)) (Prims.of_int (6))
                                (Prims.of_int (175)) (Prims.of_int (39)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (171)) (Prims.of_int (6))
                                      (Prims.of_int (175))
                                      (Prims.of_int (39)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (171)) (Prims.of_int (6))
                                      (Prims.of_int (175))
                                      (Prims.of_int (39)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (173))
                                            (Prims.of_int (8))
                                            (Prims.of_int (173))
                                            (Prims.of_int (29)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (171))
                                            (Prims.of_int (6))
                                            (Prims.of_int (175))
                                            (Prims.of_int (39)))))
                                   (Obj.magic (term_to_string head))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (171))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (175))
                                                       (Prims.of_int (39)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (171))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (175))
                                                       (Prims.of_int (39)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (172))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (172))
                                                             (Prims.of_int (33)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Printf.fst"
                                                             (Prims.of_int (121))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (123))
                                                             (Prims.of_int (44)))))
                                                    (Obj.magic
                                                       (binder_to_string
                                                          binder))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            fun x ->
                                                              fun x1 ->
                                                                fun x2 ->
                                                                  Prims.strcat
                                                                    (
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "let tot "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " = "))
                                                                    (Prims.strcat
                                                                    x ";\n"))
                                                                    (Prims.strcat
                                                                    x1 ""))
                                                                    (
                                                                    Prims.strcat
                                                                    x2 "")))))
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
      | Pulse_Syntax_Base.Tm_Abs
          { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
            Pulse_Syntax_Base.ascription = c;
            Pulse_Syntax_Base.body = body;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (183)) (Prims.of_int (14))
                     (Prims.of_int (183)) (Prims.of_int (54)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (178)) (Prims.of_int (6))
                     (Prims.of_int (183)) (Prims.of_int (54)))))
            (Obj.magic (st_term_to_string' (indent level) body))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (178)) (Prims.of_int (6))
                                (Prims.of_int (183)) (Prims.of_int (54)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (178)) (Prims.of_int (6))
                                (Prims.of_int (183)) (Prims.of_int (54)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (178)) (Prims.of_int (6))
                                      (Prims.of_int (183))
                                      (Prims.of_int (54)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (178)) (Prims.of_int (6))
                                      (Prims.of_int (183))
                                      (Prims.of_int (54)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (181))
                                            (Prims.of_int (14))
                                            (Prims.of_int (181))
                                            (Prims.of_int (32)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (178))
                                            (Prims.of_int (6))
                                            (Prims.of_int (183))
                                            (Prims.of_int (54)))))
                                   (Obj.magic (comp_to_string c))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (178))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (183))
                                                       (Prims.of_int (54)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (178))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (183))
                                                       (Prims.of_int (54)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (180))
                                                             (Prims.of_int (14))
                                                             (Prims.of_int (180))
                                                             (Prims.of_int (34)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Printf.fst"
                                                             (Prims.of_int (121))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (123))
                                                             (Prims.of_int (44)))))
                                                    (Obj.magic
                                                       (binder_to_string b))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            fun x ->
                                                              fun x1 ->
                                                                fun x2 ->
                                                                  Prims.strcat
                                                                    (
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "(fun ("
                                                                    (Prims.strcat
                                                                    (qual_to_string
                                                                    q) ""))
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    ")\n"))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\n {\n"))
                                                                    (Prims.strcat
                                                                    x1 ""))
                                                                    (
                                                                    Prims.strcat
                                                                    x2 "\n}")))))
                                              (fun uu___2 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 ->
                                                      uu___2 uu___1))))
                                        uu___1)))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 -> uu___1 (indent level)))))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> uu___1 uu___)))) uu___)
      | Pulse_Syntax_Base.Tm_If
          { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
            Pulse_Syntax_Base.else_ = else_;
            Pulse_Syntax_Base.post1 = uu___;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (186)) (Prims.of_int (6))
                     (Prims.of_int (196)) (Prims.of_int (13)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (186)) (Prims.of_int (6))
                     (Prims.of_int (196)) (Prims.of_int (13)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                           (Prims.of_int (195)) (Prims.of_int (8))
                           (Prims.of_int (195)) (Prims.of_int (49)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                           (Prims.of_int (186)) (Prims.of_int (6))
                           (Prims.of_int (196)) (Prims.of_int (13)))))
                  (Obj.magic (st_term_to_string' (indent level) else_))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (186)) (Prims.of_int (6))
                                      (Prims.of_int (196))
                                      (Prims.of_int (13)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (186)) (Prims.of_int (6))
                                      (Prims.of_int (196))
                                      (Prims.of_int (13)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (186))
                                            (Prims.of_int (6))
                                            (Prims.of_int (196))
                                            (Prims.of_int (13)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (186))
                                            (Prims.of_int (6))
                                            (Prims.of_int (196))
                                            (Prims.of_int (13)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Syntax.Printer.fst"
                                                  (Prims.of_int (186))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (196))
                                                  (Prims.of_int (13)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Syntax.Printer.fst"
                                                  (Prims.of_int (186))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (196))
                                                  (Prims.of_int (13)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Syntax.Printer.fst"
                                                        (Prims.of_int (186))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (196))
                                                        (Prims.of_int (13)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Syntax.Printer.fst"
                                                        (Prims.of_int (186))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (196))
                                                        (Prims.of_int (13)))))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Syntax.Printer.fst"
                                                              (Prims.of_int (186))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (196))
                                                              (Prims.of_int (13)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Syntax.Printer.fst"
                                                              (Prims.of_int (186))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (196))
                                                              (Prims.of_int (13)))))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (49)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (13)))))
                                                           (Obj.magic
                                                              (st_term_to_string'
                                                                 (indent
                                                                    level)
                                                                 then_))
                                                           (fun uu___2 ->
                                                              (fun uu___2 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (term_to_string
                                                                    b))
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
                                                                    fun x6 ->
                                                                    fun x7 ->
                                                                    fun x8 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "if ("
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    ")\n"))
                                                                    (Prims.strcat
                                                                    x "{\n"))
                                                                    (Prims.strcat
                                                                    x1 ""))
                                                                    (Prims.strcat
                                                                    x2 "\n"))
                                                                    (Prims.strcat
                                                                    x3 "}\n"))
                                                                    (Prims.strcat
                                                                    x4
                                                                    "else\n"))
                                                                    (Prims.strcat
                                                                    x5 "{\n"))
                                                                    (Prims.strcat
                                                                    x6 ""))
                                                                    (Prims.strcat
                                                                    x7 "\n"))
                                                                    (Prims.strcat
                                                                    x8 "}")))))
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
                                                                    (indent
                                                                    level)))))
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
                                                       uu___2 level))))
                                         (fun uu___2 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 -> uu___2 level))))
                                   (fun uu___2 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___3 -> uu___2 (indent level)))))
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> uu___2 uu___1)))) uu___1)))
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> uu___1 level))
      | Pulse_Syntax_Base.Tm_Match
          { Pulse_Syntax_Base.sc = sc; Pulse_Syntax_Base.returns_ = uu___;
            Pulse_Syntax_Base.brs = brs;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (201)) (Prims.of_int (8))
                     (Prims.of_int (201)) (Prims.of_int (32)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (199)) (Prims.of_int (6))
                     (Prims.of_int (201)) (Prims.of_int (32)))))
            (Obj.magic (branches_to_string brs))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (199)) (Prims.of_int (6))
                                (Prims.of_int (201)) (Prims.of_int (32)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (199)) (Prims.of_int (6))
                                (Prims.of_int (201)) (Prims.of_int (32)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (200)) (Prims.of_int (8))
                                      (Prims.of_int (200))
                                      (Prims.of_int (27)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "FStar.Printf.fst"
                                      (Prims.of_int (121)) (Prims.of_int (8))
                                      (Prims.of_int (123))
                                      (Prims.of_int (44)))))
                             (Obj.magic (term_to_string sc))
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     fun x ->
                                       Prims.strcat
                                         (Prims.strcat "match ("
                                            (Prims.strcat uu___2 ") with "))
                                         (Prims.strcat x "")))))
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> uu___2 uu___1)))) uu___1)
      | Pulse_Syntax_Base.Tm_IntroPure { Pulse_Syntax_Base.p = p;_} ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (206)) (Prims.of_int (8))
                     (Prims.of_int (206)) (Prims.of_int (42)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                     (Prims.of_int (19)) (Prims.of_int (590))
                     (Prims.of_int (31)))))
            (Obj.magic (term_to_string' (indent level) p))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    Prims.strcat
                      (Prims.strcat "introduce pure (\n"
                         (Prims.strcat (indent level) ""))
                      (Prims.strcat uu___ ")")))
      | Pulse_Syntax_Base.Tm_ElimExists { Pulse_Syntax_Base.p1 = p;_} ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (210)) (Prims.of_int (8))
                     (Prims.of_int (210)) (Prims.of_int (26)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                     (Prims.of_int (19)) (Prims.of_int (590))
                     (Prims.of_int (31))))) (Obj.magic (term_to_string p))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    Prims.strcat "elim_exists " (Prims.strcat uu___ "")))
      | Pulse_Syntax_Base.Tm_IntroExists
          { Pulse_Syntax_Base.p2 = p;
            Pulse_Syntax_Base.witnesses = witnesses;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (217)) (Prims.of_int (8))
                     (Prims.of_int (217)) (Prims.of_int (43)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (213)) (Prims.of_int (6))
                     (Prims.of_int (217)) (Prims.of_int (43)))))
            (Obj.magic (term_list_to_string " " witnesses))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (213)) (Prims.of_int (6))
                                (Prims.of_int (217)) (Prims.of_int (43)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (213)) (Prims.of_int (6))
                                (Prims.of_int (217)) (Prims.of_int (43)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (213)) (Prims.of_int (6))
                                      (Prims.of_int (217))
                                      (Prims.of_int (43)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (213)) (Prims.of_int (6))
                                      (Prims.of_int (217))
                                      (Prims.of_int (43)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (215))
                                            (Prims.of_int (8))
                                            (Prims.of_int (215))
                                            (Prims.of_int (42)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Printf.fst"
                                            (Prims.of_int (121))
                                            (Prims.of_int (8))
                                            (Prims.of_int (123))
                                            (Prims.of_int (44)))))
                                   (Obj.magic
                                      (term_to_string' (indent level) p))
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           fun x ->
                                             fun x1 ->
                                               Prims.strcat
                                                 (Prims.strcat
                                                    (Prims.strcat
                                                       (Prims.strcat
                                                          "introduce\n"
                                                          (Prims.strcat
                                                             (indent level)
                                                             ""))
                                                       (Prims.strcat uu___1
                                                          "\n"))
                                                    (Prims.strcat x "with "))
                                                 (Prims.strcat x1 "")))))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 -> uu___1 level))))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> uu___1 uu___)))) uu___)
      | Pulse_Syntax_Base.Tm_While
          { Pulse_Syntax_Base.invariant = invariant;
            Pulse_Syntax_Base.condition = condition;
            Pulse_Syntax_Base.condition_var = uu___;
            Pulse_Syntax_Base.body3 = body;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (220)) (Prims.of_int (6))
                     (Prims.of_int (227)) (Prims.of_int (13)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (220)) (Prims.of_int (6))
                     (Prims.of_int (227)) (Prims.of_int (13)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                           (Prims.of_int (226)) (Prims.of_int (8))
                           (Prims.of_int (226)) (Prims.of_int (48)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                           (Prims.of_int (220)) (Prims.of_int (6))
                           (Prims.of_int (227)) (Prims.of_int (13)))))
                  (Obj.magic (st_term_to_string' (indent level) body))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (220)) (Prims.of_int (6))
                                      (Prims.of_int (227))
                                      (Prims.of_int (13)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (220)) (Prims.of_int (6))
                                      (Prims.of_int (227))
                                      (Prims.of_int (13)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (220))
                                            (Prims.of_int (6))
                                            (Prims.of_int (227))
                                            (Prims.of_int (13)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (220))
                                            (Prims.of_int (6))
                                            (Prims.of_int (227))
                                            (Prims.of_int (13)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Syntax.Printer.fst"
                                                  (Prims.of_int (220))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (227))
                                                  (Prims.of_int (13)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Syntax.Printer.fst"
                                                  (Prims.of_int (220))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (227))
                                                  (Prims.of_int (13)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Syntax.Printer.fst"
                                                        (Prims.of_int (223))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (223))
                                                        (Prims.of_int (34)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Syntax.Printer.fst"
                                                        (Prims.of_int (220))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (227))
                                                        (Prims.of_int (13)))))
                                               (Obj.magic
                                                  (term_to_string invariant))
                                               (fun uu___2 ->
                                                  (fun uu___2 ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Syntax.Printer.fst"
                                                                   (Prims.of_int (220))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (227))
                                                                   (Prims.of_int (13)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Syntax.Printer.fst"
                                                                   (Prims.of_int (220))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (227))
                                                                   (Prims.of_int (13)))))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (13)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (13)))))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (st_term_to_string'
                                                                    level
                                                                    condition))
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
                                                                    "while ("
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    ")\n"))
                                                                    (Prims.strcat
                                                                    x
                                                                    "invariant "))
                                                                    (Prims.strcat
                                                                    x1 "\n"))
                                                                    (Prims.strcat
                                                                    x2 "{\n"))
                                                                    (Prims.strcat
                                                                    x3 ""))
                                                                    (Prims.strcat
                                                                    x4 "\n"))
                                                                    (Prims.strcat
                                                                    x5 "}")))))
                                                                (fun uu___3
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    level))))
                                                          (fun uu___3 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___4 ->
                                                                  uu___3
                                                                    uu___2))))
                                                    uu___2)))
                                         (fun uu___2 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 -> uu___2 level))))
                                   (fun uu___2 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___3 -> uu___2 (indent level)))))
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> uu___2 uu___1)))) uu___1)))
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> uu___1 level))
      | Pulse_Syntax_Base.Tm_Par
          { Pulse_Syntax_Base.pre1 = pre1; Pulse_Syntax_Base.body11 = body1;
            Pulse_Syntax_Base.post11 = post1; Pulse_Syntax_Base.pre2 = pre2;
            Pulse_Syntax_Base.body21 = body2;
            Pulse_Syntax_Base.post2 = post2;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (236)) (Prims.of_int (8))
                     (Prims.of_int (236)) (Prims.of_int (30)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (230)) (Prims.of_int (6))
                     (Prims.of_int (236)) (Prims.of_int (30)))))
            (Obj.magic (term_to_string post2))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (230)) (Prims.of_int (6))
                                (Prims.of_int (236)) (Prims.of_int (30)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (230)) (Prims.of_int (6))
                                (Prims.of_int (236)) (Prims.of_int (30)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (235)) (Prims.of_int (8))
                                      (Prims.of_int (235))
                                      (Prims.of_int (40)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (230)) (Prims.of_int (6))
                                      (Prims.of_int (236))
                                      (Prims.of_int (30)))))
                             (Obj.magic (st_term_to_string' level body2))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (230))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (236))
                                                 (Prims.of_int (30)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (230))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (236))
                                                 (Prims.of_int (30)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (234))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (234))
                                                       (Prims.of_int (29)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (230))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (236))
                                                       (Prims.of_int (30)))))
                                              (Obj.magic
                                                 (term_to_string pre2))
                                              (fun uu___2 ->
                                                 (fun uu___2 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Syntax.Printer.fst"
                                                                  (Prims.of_int (230))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (236))
                                                                  (Prims.of_int (30)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Syntax.Printer.fst"
                                                                  (Prims.of_int (230))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (236))
                                                                  (Prims.of_int (30)))))
                                                         (Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (30)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (30)))))
                                                               (Obj.magic
                                                                  (term_to_string
                                                                    post1))
                                                               (fun uu___3 ->
                                                                  (fun uu___3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (st_term_to_string'
                                                                    level
                                                                    body1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (term_to_string
                                                                    pre1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    fun x3 ->
                                                                    fun x4 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "par (<"
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    "> ("))
                                                                    (Prims.strcat
                                                                    x ") <"))
                                                                    (Prims.strcat
                                                                    x1 ") (<"))
                                                                    (Prims.strcat
                                                                    x2 "> ("))
                                                                    (Prims.strcat
                                                                    x3 ") <"))
                                                                    (Prims.strcat
                                                                    x4 ")")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    uu___4))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                    uu___3)))
                                                         (fun uu___3 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___4 ->
                                                                 uu___3
                                                                   uu___2))))
                                                   uu___2)))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 -> uu___2 uu___1))))
                                  uu___1)))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> uu___1 uu___)))) uu___)
      | Pulse_Syntax_Base.Tm_Rewrite
          { Pulse_Syntax_Base.t1 = t1; Pulse_Syntax_Base.t2 = t2;_} ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (241)) (Prims.of_int (15))
                     (Prims.of_int (241)) (Prims.of_int (34)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (239)) (Prims.of_int (7))
                     (Prims.of_int (241)) (Prims.of_int (34)))))
            (Obj.magic (term_to_string t2))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (239)) (Prims.of_int (7))
                                (Prims.of_int (241)) (Prims.of_int (34)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (239)) (Prims.of_int (7))
                                (Prims.of_int (241)) (Prims.of_int (34)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (240)) (Prims.of_int (8))
                                      (Prims.of_int (240))
                                      (Prims.of_int (27)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "FStar.Printf.fst"
                                      (Prims.of_int (121)) (Prims.of_int (8))
                                      (Prims.of_int (123))
                                      (Prims.of_int (44)))))
                             (Obj.magic (term_to_string t1))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     fun x ->
                                       Prims.strcat
                                         (Prims.strcat "rewrite "
                                            (Prims.strcat uu___1 " "))
                                         (Prims.strcat x "")))))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> uu___1 uu___)))) uu___)
      | Pulse_Syntax_Base.Tm_WithLocal
          { Pulse_Syntax_Base.binder2 = binder;
            Pulse_Syntax_Base.initializer1 = initializer1;
            Pulse_Syntax_Base.body4 = body;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (248)) (Prims.of_int (8))
                     (Prims.of_int (248)) (Prims.of_int (39)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (244)) (Prims.of_int (6))
                     (Prims.of_int (248)) (Prims.of_int (39)))))
            (Obj.magic (st_term_to_string' level body))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (244)) (Prims.of_int (6))
                                (Prims.of_int (248)) (Prims.of_int (39)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (244)) (Prims.of_int (6))
                                (Prims.of_int (248)) (Prims.of_int (39)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (244)) (Prims.of_int (6))
                                      (Prims.of_int (248))
                                      (Prims.of_int (39)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (244)) (Prims.of_int (6))
                                      (Prims.of_int (248))
                                      (Prims.of_int (39)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (246))
                                            (Prims.of_int (8))
                                            (Prims.of_int (246))
                                            (Prims.of_int (36)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (244))
                                            (Prims.of_int (6))
                                            (Prims.of_int (248))
                                            (Prims.of_int (39)))))
                                   (Obj.magic (term_to_string initializer1))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (244))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (248))
                                                       (Prims.of_int (39)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (244))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (248))
                                                       (Prims.of_int (39)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (245))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (245))
                                                             (Prims.of_int (33)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Printf.fst"
                                                             (Prims.of_int (121))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (123))
                                                             (Prims.of_int (44)))))
                                                    (Obj.magic
                                                       (binder_to_string
                                                          binder))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            fun x ->
                                                              fun x1 ->
                                                                fun x2 ->
                                                                  Prims.strcat
                                                                    (
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "let mut "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " = "))
                                                                    (Prims.strcat
                                                                    x ";\n"))
                                                                    (Prims.strcat
                                                                    x1 ""))
                                                                    (
                                                                    Prims.strcat
                                                                    x2 "")))))
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
      | Pulse_Syntax_Base.Tm_Admit
          { Pulse_Syntax_Base.ctag1 = ctag; Pulse_Syntax_Base.u1 = u;
            Pulse_Syntax_Base.typ = typ; Pulse_Syntax_Base.post3 = post;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (258)) (Prims.of_int (8))
                     (Prims.of_int (260)) (Prims.of_int (60)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (251)) (Prims.of_int (6))
                     (Prims.of_int (260)) (Prims.of_int (60)))))
            (match post with
             | FStar_Pervasives_Native.None ->
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
             | FStar_Pervasives_Native.Some post1 ->
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Syntax.Printer.fst"
                                  (Prims.of_int (260)) (Prims.of_int (38))
                                  (Prims.of_int (260)) (Prims.of_int (59)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (590)) (Prims.of_int (19))
                                  (Prims.of_int (590)) (Prims.of_int (31)))))
                         (Obj.magic (term_to_string post1))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Prims.strcat " " (Prims.strcat uu___ ""))))))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (251)) (Prims.of_int (6))
                                (Prims.of_int (260)) (Prims.of_int (60)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (251)) (Prims.of_int (6))
                                (Prims.of_int (260)) (Prims.of_int (60)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (257)) (Prims.of_int (8))
                                      (Prims.of_int (257))
                                      (Prims.of_int (28)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "FStar.Printf.fst"
                                      (Prims.of_int (121)) (Prims.of_int (8))
                                      (Prims.of_int (123))
                                      (Prims.of_int (44)))))
                             (Obj.magic (term_to_string typ))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     fun x ->
                                       Prims.strcat
                                         (Prims.strcat
                                            (Prims.strcat
                                               (Prims.strcat ""
                                                  (Prims.strcat
                                                     (match ctag with
                                                      | Pulse_Syntax_Base.STT
                                                          -> "stt_admit"
                                                      | Pulse_Syntax_Base.STT_Atomic
                                                          ->
                                                          "stt_atomic_admit"
                                                      | Pulse_Syntax_Base.STT_Ghost
                                                          ->
                                                          "stt_ghost_admit")
                                                     "<"))
                                               (Prims.strcat
                                                  (universe_to_string
                                                     Prims.int_zero u) "> "))
                                            (Prims.strcat uu___1 ""))
                                         (Prims.strcat x "")))))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> uu___1 uu___)))) uu___)
      | Pulse_Syntax_Base.Tm_ProofHintWithBinders
          { Pulse_Syntax_Base.hint_type = uu___;
            Pulse_Syntax_Base.binders = binders; Pulse_Syntax_Base.v = v;
            Pulse_Syntax_Base.t3 = t1;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (268)) (Prims.of_int (8))
                     (Prims.of_int (268)) (Prims.of_int (36)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (263)) (Prims.of_int (6))
                     (Prims.of_int (268)) (Prims.of_int (36)))))
            (Obj.magic (st_term_to_string' level t1))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (263)) (Prims.of_int (6))
                                (Prims.of_int (268)) (Prims.of_int (36)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (263)) (Prims.of_int (6))
                                (Prims.of_int (268)) (Prims.of_int (36)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (267)) (Prims.of_int (8))
                                      (Prims.of_int (267))
                                      (Prims.of_int (26)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "FStar.Printf.fst"
                                      (Prims.of_int (121)) (Prims.of_int (8))
                                      (Prims.of_int (123))
                                      (Prims.of_int (44)))))
                             (Obj.magic (term_to_string v))
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     fun x ->
                                       Prims.strcat
                                         (Prims.strcat
                                            (Prims.strcat "assert "
                                               (Prims.strcat
                                                  (if
                                                     (FStar_List_Tot_Base.length
                                                        binders)
                                                       = Prims.int_zero
                                                   then ""
                                                   else
                                                     Prims.strcat ""
                                                       (Prims.strcat
                                                          (FStar_List_Tot_Base.fold_left
                                                             (fun s ->
                                                                fun _b ->
                                                                  Prims.strcat
                                                                    ""
                                                                    (
                                                                    Prims.strcat
                                                                    s " _"))
                                                             "" binders) "."))
                                                  ""))
                                            (Prims.strcat uu___2 " in\n"))
                                         (Prims.strcat x "")))))
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> uu___2 uu___1)))) uu___1)
      | Pulse_Syntax_Base.Tm_WithInv
          { Pulse_Syntax_Base.name1 = name; Pulse_Syntax_Base.body5 = body;
            Pulse_Syntax_Base.returns_inv = uu___;_}
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (273)) (Prims.of_int (8))
                     (Prims.of_int (273)) (Prims.of_int (48)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (271)) (Prims.of_int (6))
                     (Prims.of_int (273)) (Prims.of_int (48)))))
            (Obj.magic (st_term_to_string' (indent level) body))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (271)) (Prims.of_int (6))
                                (Prims.of_int (273)) (Prims.of_int (48)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (271)) (Prims.of_int (6))
                                (Prims.of_int (273)) (Prims.of_int (48)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (272)) (Prims.of_int (8))
                                      (Prims.of_int (272))
                                      (Prims.of_int (29)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "FStar.Printf.fst"
                                      (Prims.of_int (121)) (Prims.of_int (8))
                                      (Prims.of_int (123))
                                      (Prims.of_int (44)))))
                             (Obj.magic (term_to_string name))
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     fun x ->
                                       Prims.strcat
                                         (Prims.strcat "with_invariant "
                                            (Prims.strcat uu___2 ". {\n"))
                                         (Prims.strcat x "\n}")))))
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> uu___2 uu___1)))) uu___1)
and (branches_to_string :
  (Pulse_Syntax_Base.pattern * Pulse_Syntax_Base.st_term) Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun brs ->
       match brs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | b::bs ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (279)) (Prims.of_int (13))
                            (Prims.of_int (279)) (Prims.of_int (31)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (279)) (Prims.of_int (13))
                            (Prims.of_int (279)) (Prims.of_int (55)))))
                   (Obj.magic (branch_to_string b))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (279))
                                       (Prims.of_int (34))
                                       (Prims.of_int (279))
                                       (Prims.of_int (55)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "prims.fst"
                                       (Prims.of_int (590))
                                       (Prims.of_int (19))
                                       (Prims.of_int (590))
                                       (Prims.of_int (31)))))
                              (Obj.magic (branches_to_string bs))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> Prims.strcat uu___ uu___1))))
                        uu___)))) uu___
and (branch_to_string :
  (Pulse_Syntax_Base.pattern * Pulse_Syntax_Base.st_term) ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun br ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (282)) (Prims.of_int (17)) (Prims.of_int (282))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (281)) (Prims.of_int (35)) (Prims.of_int (283))
               (Prims.of_int (25)))))
      (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> br))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (pat, e) -> Obj.magic (st_term_to_string' "" e)) uu___)
let (st_term_to_string :
  Pulse_Syntax_Base.st_term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> st_term_to_string' "" t
let (tag_of_term : Pulse_Syntax_Base.term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_Emp -> "Tm_Emp"
    | Pulse_Syntax_Base.Tm_Inv uu___ -> "Tm_Inv"
    | Pulse_Syntax_Base.Tm_Pure uu___ -> "Tm_Pure"
    | Pulse_Syntax_Base.Tm_Star (uu___, uu___1) -> "Tm_Star"
    | Pulse_Syntax_Base.Tm_ExistsSL (uu___, uu___1, uu___2) -> "Tm_ExistsSL"
    | Pulse_Syntax_Base.Tm_ForallSL (uu___, uu___1, uu___2) -> "Tm_ForallSL"
    | Pulse_Syntax_Base.Tm_VProp -> "Tm_VProp"
    | Pulse_Syntax_Base.Tm_Inames -> "Tm_Inames"
    | Pulse_Syntax_Base.Tm_EmpInames -> "Tm_EmpInames"
    | Pulse_Syntax_Base.Tm_Unknown -> "Tm_Unknown"
    | Pulse_Syntax_Base.Tm_FStar uu___ -> "Tm_FStar"
let (tag_of_st_term : Pulse_Syntax_Base.st_term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Return uu___ -> "Tm_Return"
    | Pulse_Syntax_Base.Tm_Abs uu___ -> "Tm_Abs"
    | Pulse_Syntax_Base.Tm_STApp uu___ -> "Tm_STApp"
    | Pulse_Syntax_Base.Tm_Bind uu___ -> "Tm_Bind"
    | Pulse_Syntax_Base.Tm_TotBind uu___ -> "Tm_TotBind"
    | Pulse_Syntax_Base.Tm_If uu___ -> "Tm_If"
    | Pulse_Syntax_Base.Tm_Match uu___ -> "Tm_Match"
    | Pulse_Syntax_Base.Tm_IntroPure uu___ -> "Tm_IntroPure"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "Tm_ElimExists"
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "Tm_IntroExists"
    | Pulse_Syntax_Base.Tm_While uu___ -> "Tm_While"
    | Pulse_Syntax_Base.Tm_Par uu___ -> "Tm_Par"
    | Pulse_Syntax_Base.Tm_WithLocal uu___ -> "Tm_WithLocal"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Tm_Rewrite"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Tm_Admit"
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___ ->
        "Tm_ProofHintWithBinders"
    | Pulse_Syntax_Base.Tm_WithInv uu___ -> "Tm_WithInv"
let (tag_of_comp :
  Pulse_Syntax_Base.comp ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun c ->
       match c with
       | Pulse_Syntax_Base.C_Tot uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "Total")))
       | Pulse_Syntax_Base.C_ST uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "ST")))
       | Pulse_Syntax_Base.C_STAtomic (i, uu___) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (326)) (Prims.of_int (31))
                            (Prims.of_int (326)) (Prims.of_int (49)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic (term_to_string i))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "Atomic " (Prims.strcat uu___1 "")))))
       | Pulse_Syntax_Base.C_STGhost (i, uu___) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (328)) (Prims.of_int (30))
                            (Prims.of_int (328)) (Prims.of_int (48)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic (term_to_string i))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "Ghost " (Prims.strcat uu___1 ""))))))
      uu___
let rec (print_st_head : Pulse_Syntax_Base.st_term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Abs uu___ -> "Abs"
    | Pulse_Syntax_Base.Tm_Return p -> print_head p.Pulse_Syntax_Base.term
    | Pulse_Syntax_Base.Tm_Bind uu___ -> "Bind"
    | Pulse_Syntax_Base.Tm_TotBind uu___ -> "TotBind"
    | Pulse_Syntax_Base.Tm_If uu___ -> "If"
    | Pulse_Syntax_Base.Tm_Match uu___ -> "Match"
    | Pulse_Syntax_Base.Tm_While uu___ -> "While"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Admit"
    | Pulse_Syntax_Base.Tm_Par uu___ -> "Par"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Rewrite"
    | Pulse_Syntax_Base.Tm_WithLocal uu___ -> "WithLocal"
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = p; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_IntroPure uu___ -> "IntroPure"
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "IntroExists"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "ElimExists"
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___ -> "AssertWithBinders"
    | Pulse_Syntax_Base.Tm_WithInv uu___ -> "WithInv"
and (print_head : Pulse_Syntax_Base.term -> Prims.string) =
  fun t -> "<pure term>"
let rec (print_skel : Pulse_Syntax_Base.st_term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Abs
        { Pulse_Syntax_Base.b = uu___; Pulse_Syntax_Base.q = uu___1;
          Pulse_Syntax_Base.ascription = uu___2;
          Pulse_Syntax_Base.body = body;_}
        -> Prims.strcat "(fun _ -> " (Prims.strcat (print_skel body) ")")
    | Pulse_Syntax_Base.Tm_Return
        { Pulse_Syntax_Base.ctag = uu___;
          Pulse_Syntax_Base.insert_eq = uu___1; Pulse_Syntax_Base.term = p;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_Bind
        { Pulse_Syntax_Base.binder = uu___; Pulse_Syntax_Base.head1 = e1;
          Pulse_Syntax_Base.body1 = e2;_}
        ->
        Prims.strcat
          (Prims.strcat "(Bind " (Prims.strcat (print_skel e1) " "))
          (Prims.strcat (print_skel e2) ")")
    | Pulse_Syntax_Base.Tm_TotBind
        { Pulse_Syntax_Base.binder1 = uu___;
          Pulse_Syntax_Base.head2 = uu___1; Pulse_Syntax_Base.body2 = e2;_}
        -> Prims.strcat "(TotBind _ " (Prims.strcat (print_skel e2) ")")
    | Pulse_Syntax_Base.Tm_If uu___ -> "If"
    | Pulse_Syntax_Base.Tm_Match uu___ -> "Match"
    | Pulse_Syntax_Base.Tm_While uu___ -> "While"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Admit"
    | Pulse_Syntax_Base.Tm_Par uu___ -> "Par"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Rewrite"
    | Pulse_Syntax_Base.Tm_WithLocal uu___ -> "WithLocal"
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = p; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_IntroPure uu___ -> "IntroPure"
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "IntroExists"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "ElimExists"
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___ -> "AssertWithBinders"
    | Pulse_Syntax_Base.Tm_WithInv uu___ -> "WithInv"