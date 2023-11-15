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
let (qual_to_doc :
  Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Implicit) ->
        FStar_Pprint.doc_of_string "#"
let (qual_to_string :
  Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Implicit) -> "#"
let (indent : Prims.string -> Prims.string) =
  fun level -> Prims.strcat level "\t"
let rec (term_to_doc :
  Pulse_Syntax_Base.term ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match t.Pulse_Syntax_Base.t with
       | Pulse_Syntax_Base.Tm_Emp ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "emp")))
       | Pulse_Syntax_Base.Tm_Pure p ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (57)) (Prims.of_int (44))
                            (Prims.of_int (57)) (Prims.of_int (66)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (57)) (Prims.of_int (19))
                            (Prims.of_int (57)) (Prims.of_int (66)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Syntax.Printer.fst"
                                  (Prims.of_int (57)) (Prims.of_int (51))
                                  (Prims.of_int (57)) (Prims.of_int (66)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Syntax.Printer.fst"
                                  (Prims.of_int (57)) (Prims.of_int (44))
                                  (Prims.of_int (57)) (Prims.of_int (66)))))
                         (Obj.magic (term_to_doc p))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> FStar_Pprint.parens uu___))))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           FStar_Pprint.op_Hat_Slash_Hat
                             (FStar_Pprint.doc_of_string "pure") uu___))))
       | Pulse_Syntax_Base.Tm_Star (p1, p2) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (60)) (Prims.of_int (16))
                            (Prims.of_int (60)) (Prims.of_int (32)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (59)) (Prims.of_int (6))
                            (Prims.of_int (61)) (Prims.of_int (32)))))
                   (Obj.magic (term_to_doc p1))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (61))
                                       (Prims.of_int (16))
                                       (Prims.of_int (61))
                                       (Prims.of_int (32)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (59)) (Prims.of_int (6))
                                       (Prims.of_int (61))
                                       (Prims.of_int (32)))))
                              (Obj.magic (term_to_doc p2))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      FStar_Pprint.infix (Prims.of_int (2))
                                        Prims.int_one
                                        (FStar_Pprint.doc_of_string "**")
                                        uu___ uu___1)))) uu___)))
       | Pulse_Syntax_Base.Tm_ExistsSL (uu___, b, body) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (64)) (Prims.of_int (17))
                            (Prims.of_int (69)) (Prims.of_int (37)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (64)) (Prims.of_int (6))
                            (Prims.of_int (70)) (Prims.of_int (26)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Syntax.Printer.fst"
                                  (Prims.of_int (65)) (Prims.of_int (8))
                                  (Prims.of_int (68)) (Prims.of_int (81)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Syntax.Printer.fst"
                                  (Prims.of_int (64)) (Prims.of_int (17))
                                  (Prims.of_int (69)) (Prims.of_int (37)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (65))
                                        (Prims.of_int (14))
                                        (Prims.of_int (68))
                                        (Prims.of_int (81)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (65))
                                        (Prims.of_int (8))
                                        (Prims.of_int (68))
                                        (Prims.of_int (81)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Syntax.Printer.fst"
                                              (Prims.of_int (66))
                                              (Prims.of_int (28))
                                              (Prims.of_int (68))
                                              (Prims.of_int (80)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Syntax.Printer.fst"
                                              (Prims.of_int (65))
                                              (Prims.of_int (14))
                                              (Prims.of_int (68))
                                              (Prims.of_int (81)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (66))
                                                    (Prims.of_int (36))
                                                    (Prims.of_int (68))
                                                    (Prims.of_int (79)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (66))
                                                    (Prims.of_int (28))
                                                    (Prims.of_int (68))
                                                    (Prims.of_int (80)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (66))
                                                          (Prims.of_int (37))
                                                          (Prims.of_int (66))
                                                          (Prims.of_int (82)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (66))
                                                          (Prims.of_int (36))
                                                          (Prims.of_int (68))
                                                          (Prims.of_int (79)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (66))
                                                                (Prims.of_int (51))
                                                                (Prims.of_int (66))
                                                                (Prims.of_int (82)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (66))
                                                                (Prims.of_int (37))
                                                                (Prims.of_int (66))
                                                                (Prims.of_int (82)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Unseal.unseal
                                                             (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               FStar_Pprint.doc_of_string
                                                                 uu___1))))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (78)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (79)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (78)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (78)))))
                                                                  (Obj.magic
                                                                    (term_to_doc
                                                                    b.Pulse_Syntax_Base.binder_ty))
                                                                  (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (FStar_Pprint.doc_of_string
                                                                    ":")
                                                                    uu___2))))
                                                            (fun uu___2 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___3
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___1
                                                                    uu___2))))
                                                      uu___1)))
                                           (fun uu___1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pprint.parens uu___1))))
                                     (fun uu___1 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 ->
                                             FStar_Pprint.prefix
                                               (Prims.of_int (2))
                                               Prims.int_one
                                               (FStar_Pprint.doc_of_string
                                                  "exists") uu___1))))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 -> FStar_Pprint.group uu___1))))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 FStar_Pprint.op_Hat_Hat uu___1
                                   (FStar_Pprint.doc_of_string ".")))))
                   (fun uu___1 ->
                      (fun uu___1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (70)) (Prims.of_int (8))
                                       (Prims.of_int (70))
                                       (Prims.of_int (26)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (64)) (Prims.of_int (6))
                                       (Prims.of_int (70))
                                       (Prims.of_int (26)))))
                              (Obj.magic (term_to_doc body))
                              (fun uu___2 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 ->
                                      FStar_Pprint.prefix (Prims.of_int (2))
                                        Prims.int_one uu___1 uu___2))))
                        uu___1)))
       | Pulse_Syntax_Base.Tm_ForallSL (u, b, body) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (73)) (Prims.of_int (17))
                            (Prims.of_int (78)) (Prims.of_int (37)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (73)) (Prims.of_int (6))
                            (Prims.of_int (79)) (Prims.of_int (26)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Syntax.Printer.fst"
                                  (Prims.of_int (74)) (Prims.of_int (8))
                                  (Prims.of_int (77)) (Prims.of_int (81)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Syntax.Printer.fst"
                                  (Prims.of_int (73)) (Prims.of_int (17))
                                  (Prims.of_int (78)) (Prims.of_int (37)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (74))
                                        (Prims.of_int (14))
                                        (Prims.of_int (77))
                                        (Prims.of_int (81)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (74))
                                        (Prims.of_int (8))
                                        (Prims.of_int (77))
                                        (Prims.of_int (81)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Syntax.Printer.fst"
                                              (Prims.of_int (75))
                                              (Prims.of_int (28))
                                              (Prims.of_int (77))
                                              (Prims.of_int (80)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Syntax.Printer.fst"
                                              (Prims.of_int (74))
                                              (Prims.of_int (14))
                                              (Prims.of_int (77))
                                              (Prims.of_int (81)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (75))
                                                    (Prims.of_int (36))
                                                    (Prims.of_int (77))
                                                    (Prims.of_int (79)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (75))
                                                    (Prims.of_int (28))
                                                    (Prims.of_int (77))
                                                    (Prims.of_int (80)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (75))
                                                          (Prims.of_int (37))
                                                          (Prims.of_int (75))
                                                          (Prims.of_int (82)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (75))
                                                          (Prims.of_int (36))
                                                          (Prims.of_int (77))
                                                          (Prims.of_int (79)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (75))
                                                                (Prims.of_int (51))
                                                                (Prims.of_int (75))
                                                                (Prims.of_int (82)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (75))
                                                                (Prims.of_int (37))
                                                                (Prims.of_int (75))
                                                                (Prims.of_int (82)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Unseal.unseal
                                                             (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name))
                                                       (fun uu___ ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___1 ->
                                                               FStar_Pprint.doc_of_string
                                                                 uu___))))
                                                 (fun uu___ ->
                                                    (fun uu___ ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (78)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (79)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (78)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (78)))))
                                                                  (Obj.magic
                                                                    (term_to_doc
                                                                    b.Pulse_Syntax_Base.binder_ty))
                                                                  (fun uu___1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (FStar_Pprint.doc_of_string
                                                                    ":")
                                                                    uu___1))))
                                                            (fun uu___1 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___
                                                                    uu___1))))
                                                      uu___)))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   FStar_Pprint.parens uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             FStar_Pprint.prefix
                                               (Prims.of_int (2))
                                               Prims.int_one
                                               (FStar_Pprint.doc_of_string
                                                  "forall") uu___))))
                               (fun uu___ ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 -> FStar_Pprint.group uu___))))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 FStar_Pprint.op_Hat_Hat uu___
                                   (FStar_Pprint.doc_of_string ".")))))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (79)) (Prims.of_int (8))
                                       (Prims.of_int (79))
                                       (Prims.of_int (26)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (73)) (Prims.of_int (6))
                                       (Prims.of_int (79))
                                       (Prims.of_int (26)))))
                              (Obj.magic (term_to_doc body))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      FStar_Pprint.prefix (Prims.of_int (2))
                                        Prims.int_one uu___ uu___1)))) uu___)))
       | Pulse_Syntax_Base.Tm_VProp ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "vprop")))
       | Pulse_Syntax_Base.Tm_Inames ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "inames")))
       | Pulse_Syntax_Base.Tm_EmpInames ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "emp_inames")))
       | Pulse_Syntax_Base.Tm_Unknown ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "_")))
       | Pulse_Syntax_Base.Tm_FStar t1 ->
           Obj.magic (Obj.repr (FStar_Tactics_V2_Builtins.term_to_doc t1)))
      uu___
let (term_to_string :
  Pulse_Syntax_Base.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (89)) (Prims.of_int (30)) (Prims.of_int (89))
               (Prims.of_int (45)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (89)) (Prims.of_int (23)) (Prims.of_int (89))
               (Prims.of_int (45))))) (Obj.magic (term_to_doc t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_Pprint.render uu___))
let (binder_to_doc :
  Pulse_Syntax_Base.binder ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (93)) (Prims.of_int (4)) (Prims.of_int (93))
               (Prims.of_int (49)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (93)) (Prims.of_int (4)) (Prims.of_int (93))
               (Prims.of_int (97)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (93)) (Prims.of_int (18))
                     (Prims.of_int (93)) (Prims.of_int (49)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (93)) (Prims.of_int (4))
                     (Prims.of_int (93)) (Prims.of_int (49)))))
            (Obj.magic
               (FStar_Tactics_Unseal.unseal
                  (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> FStar_Pprint.doc_of_string uu___))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (93)) (Prims.of_int (53))
                          (Prims.of_int (93)) (Prims.of_int (97)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (93)) (Prims.of_int (4))
                          (Prims.of_int (93)) (Prims.of_int (97)))))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (93)) (Prims.of_int (74))
                                (Prims.of_int (93)) (Prims.of_int (97)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (93)) (Prims.of_int (53))
                                (Prims.of_int (93)) (Prims.of_int (97)))))
                       (Obj.magic (term_to_doc b.Pulse_Syntax_Base.binder_ty))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStar_Pprint.op_Hat_Hat
                                 (FStar_Pprint.doc_of_string ":") uu___1))))
                 (fun uu___1 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 -> FStar_Pprint.op_Hat_Hat uu___ uu___1))))
           uu___)
let (binder_to_string :
  Pulse_Syntax_Base.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (99)) (Prims.of_int (12)) (Prims.of_int (99))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (97)) (Prims.of_int (4)) (Prims.of_int (99))
               (Prims.of_int (40)))))
      (Obj.magic (term_to_string b.Pulse_Syntax_Base.binder_ty))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (97)) (Prims.of_int (4))
                          (Prims.of_int (99)) (Prims.of_int (40)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (97)) (Prims.of_int (4))
                          (Prims.of_int (99)) (Prims.of_int (40)))))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (98)) (Prims.of_int (12))
                                (Prims.of_int (98)) (Prims.of_int (43)))))
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
let (comp_to_doc :
  Pulse_Syntax_Base.comp ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun c ->
    match c with
    | Pulse_Syntax_Base.C_Tot t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (112)) (Prims.of_int (13))
                   (Prims.of_int (114)) (Prims.of_int (7)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (112)) (Prims.of_int (6))
                   (Prims.of_int (114)) (Prims.of_int (7)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (113)) (Prims.of_int (30))
                         (Prims.of_int (113)) (Prims.of_int (43)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (112)) (Prims.of_int (13))
                         (Prims.of_int (114)) (Prims.of_int (7)))))
                (Obj.magic (term_to_doc t))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        FStar_Pprint.op_Hat_Slash_Hat
                          (FStar_Pprint.doc_of_string "Tot") uu___))))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_Pprint.nest (Prims.of_int (2)) uu___))
    | Pulse_Syntax_Base.C_ST s ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (117)) (Prims.of_int (13))
                   (Prims.of_int (121)) (Prims.of_int (7)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (117)) (Prims.of_int (6))
                   (Prims.of_int (121)) (Prims.of_int (7)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (118)) (Prims.of_int (6))
                         (Prims.of_int (118)) (Prims.of_int (55)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (117)) (Prims.of_int (13))
                         (Prims.of_int (121)) (Prims.of_int (7)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (118)) (Prims.of_int (12))
                               (Prims.of_int (118)) (Prims.of_int (55)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (118)) (Prims.of_int (6))
                               (Prims.of_int (118)) (Prims.of_int (55)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (118)) (Prims.of_int (37))
                                     (Prims.of_int (118)) (Prims.of_int (54)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (118)) (Prims.of_int (12))
                                     (Prims.of_int (118)) (Prims.of_int (55)))))
                            (Obj.magic (term_to_doc s.Pulse_Syntax_Base.res))
                            (fun uu___ ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    FStar_Pprint.op_Hat_Slash_Hat
                                      (FStar_Pprint.doc_of_string "stt")
                                      uu___))))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> FStar_Pprint.group uu___))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (119)) (Prims.of_int (10))
                                    (Prims.of_int (120)) (Prims.of_int (82)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (117)) (Prims.of_int (13))
                                    (Prims.of_int (121)) (Prims.of_int (7)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (119))
                                          (Prims.of_int (10))
                                          (Prims.of_int (119))
                                          (Prims.of_int (82)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (119))
                                          (Prims.of_int (10))
                                          (Prims.of_int (120))
                                          (Prims.of_int (82)))))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (119))
                                                (Prims.of_int (17))
                                                (Prims.of_int (119))
                                                (Prims.of_int (82)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (119))
                                                (Prims.of_int (10))
                                                (Prims.of_int (119))
                                                (Prims.of_int (82)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (119))
                                                      (Prims.of_int (24))
                                                      (Prims.of_int (119))
                                                      (Prims.of_int (81)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (119))
                                                      (Prims.of_int (17))
                                                      (Prims.of_int (119))
                                                      (Prims.of_int (82)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Syntax.Printer.fst"
                                                            (Prims.of_int (119))
                                                            (Prims.of_int (32))
                                                            (Prims.of_int (119))
                                                            (Prims.of_int (80)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Syntax.Printer.fst"
                                                            (Prims.of_int (119))
                                                            (Prims.of_int (24))
                                                            (Prims.of_int (119))
                                                            (Prims.of_int (81)))))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Syntax.Printer.fst"
                                                                  (Prims.of_int (119))
                                                                  (Prims.of_int (62))
                                                                  (Prims.of_int (119))
                                                                  (Prims.of_int (79)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Syntax.Printer.fst"
                                                                  (Prims.of_int (119))
                                                                  (Prims.of_int (32))
                                                                  (Prims.of_int (119))
                                                                  (Prims.of_int (80)))))
                                                         (Obj.magic
                                                            (term_to_doc
                                                               s.Pulse_Syntax_Base.pre))
                                                         (fun uu___1 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 FStar_Pprint.op_Hat_Slash_Hat
                                                                   (FStar_Pprint.doc_of_string
                                                                    "requires")
                                                                   uu___1))))
                                                   (fun uu___1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           FStar_Pprint.parens
                                                             uu___1))))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     FStar_Pprint.group
                                                       uu___1))))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               FStar_Pprint.nest
                                                 (Prims.of_int (2)) uu___1))))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (120))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (120))
                                                     (Prims.of_int (82)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (119))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (120))
                                                     (Prims.of_int (82)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (120))
                                                           (Prims.of_int (17))
                                                           (Prims.of_int (120))
                                                           (Prims.of_int (82)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (120))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (120))
                                                           (Prims.of_int (82)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (120))
                                                                 (Prims.of_int (24))
                                                                 (Prims.of_int (120))
                                                                 (Prims.of_int (81)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (120))
                                                                 (Prims.of_int (17))
                                                                 (Prims.of_int (120))
                                                                 (Prims.of_int (82)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (80)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (81)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (79)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (80)))))
                                                                    (
                                                                    Obj.magic
                                                                    (term_to_doc
                                                                    s.Pulse_Syntax_Base.post))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (FStar_Pprint.doc_of_string
                                                                    "ensures")
                                                                    uu___2))))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.parens
                                                                    uu___2))))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                FStar_Pprint.group
                                                                  uu___2))))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          FStar_Pprint.nest
                                                            (Prims.of_int (2))
                                                            uu___2))))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                      uu___1 uu___2))))
                                      uu___1)))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1))))
                     uu___)))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_Pprint.nest (Prims.of_int (2)) uu___))
    | Pulse_Syntax_Base.C_STAtomic (inames, s) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (124)) (Prims.of_int (13))
                   (Prims.of_int (128)) (Prims.of_int (7)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (124)) (Prims.of_int (6))
                   (Prims.of_int (128)) (Prims.of_int (7)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (125)) (Prims.of_int (6))
                         (Prims.of_int (125)) (Prims.of_int (85)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (124)) (Prims.of_int (13))
                         (Prims.of_int (128)) (Prims.of_int (7)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (125)) (Prims.of_int (12))
                               (Prims.of_int (125)) (Prims.of_int (85)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (125)) (Prims.of_int (6))
                               (Prims.of_int (125)) (Prims.of_int (85)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (125)) (Prims.of_int (44))
                                     (Prims.of_int (125)) (Prims.of_int (84)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (125)) (Prims.of_int (12))
                                     (Prims.of_int (125)) (Prims.of_int (85)))))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (125))
                                           (Prims.of_int (44))
                                           (Prims.of_int (125))
                                           (Prims.of_int (62)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (125))
                                           (Prims.of_int (44))
                                           (Prims.of_int (125))
                                           (Prims.of_int (84)))))
                                  (Obj.magic (term_to_doc inames))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (125))
                                                      (Prims.of_int (67))
                                                      (Prims.of_int (125))
                                                      (Prims.of_int (84)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (125))
                                                      (Prims.of_int (44))
                                                      (Prims.of_int (125))
                                                      (Prims.of_int (84)))))
                                             (Obj.magic
                                                (term_to_doc
                                                   s.Pulse_Syntax_Base.res))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     FStar_Pprint.op_Hat_Slash_Hat
                                                       uu___ uu___1)))) uu___)))
                            (fun uu___ ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    FStar_Pprint.op_Hat_Slash_Hat
                                      (FStar_Pprint.doc_of_string
                                         "stt_atomic") uu___))))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> FStar_Pprint.group uu___))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (126)) (Prims.of_int (10))
                                    (Prims.of_int (127)) (Prims.of_int (73)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (124)) (Prims.of_int (13))
                                    (Prims.of_int (128)) (Prims.of_int (7)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (126))
                                          (Prims.of_int (10))
                                          (Prims.of_int (126))
                                          (Prims.of_int (73)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (126))
                                          (Prims.of_int (10))
                                          (Prims.of_int (127))
                                          (Prims.of_int (73)))))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (126))
                                                (Prims.of_int (16))
                                                (Prims.of_int (126))
                                                (Prims.of_int (73)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (126))
                                                (Prims.of_int (10))
                                                (Prims.of_int (126))
                                                (Prims.of_int (73)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (126))
                                                      (Prims.of_int (24))
                                                      (Prims.of_int (126))
                                                      (Prims.of_int (72)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (126))
                                                      (Prims.of_int (16))
                                                      (Prims.of_int (126))
                                                      (Prims.of_int (73)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Syntax.Printer.fst"
                                                            (Prims.of_int (126))
                                                            (Prims.of_int (54))
                                                            (Prims.of_int (126))
                                                            (Prims.of_int (71)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Syntax.Printer.fst"
                                                            (Prims.of_int (126))
                                                            (Prims.of_int (24))
                                                            (Prims.of_int (126))
                                                            (Prims.of_int (72)))))
                                                   (Obj.magic
                                                      (term_to_doc
                                                         s.Pulse_Syntax_Base.pre))
                                                   (fun uu___1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           FStar_Pprint.op_Hat_Slash_Hat
                                                             (FStar_Pprint.doc_of_string
                                                                "requires")
                                                             uu___1))))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     FStar_Pprint.parens
                                                       uu___1))))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               FStar_Pprint.group uu___1))))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (127))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (127))
                                                     (Prims.of_int (73)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (126))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (127))
                                                     (Prims.of_int (73)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (127))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (127))
                                                           (Prims.of_int (73)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (127))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (127))
                                                           (Prims.of_int (73)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (127))
                                                                 (Prims.of_int (24))
                                                                 (Prims.of_int (127))
                                                                 (Prims.of_int (72)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (127))
                                                                 (Prims.of_int (16))
                                                                 (Prims.of_int (127))
                                                                 (Prims.of_int (73)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (71)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (72)))))
                                                              (Obj.magic
                                                                 (term_to_doc
                                                                    s.Pulse_Syntax_Base.post))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (FStar_Pprint.doc_of_string
                                                                    "ensures")
                                                                    uu___2))))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                FStar_Pprint.parens
                                                                  uu___2))))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          FStar_Pprint.group
                                                            uu___2))))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                      uu___1 uu___2))))
                                      uu___1)))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1))))
                     uu___)))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_Pprint.nest (Prims.of_int (2)) uu___))
    | Pulse_Syntax_Base.C_STGhost (inames, s) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (131)) (Prims.of_int (13))
                   (Prims.of_int (135)) (Prims.of_int (7)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (131)) (Prims.of_int (6))
                   (Prims.of_int (135)) (Prims.of_int (7)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (132)) (Prims.of_int (6))
                         (Prims.of_int (132)) (Prims.of_int (84)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (131)) (Prims.of_int (13))
                         (Prims.of_int (135)) (Prims.of_int (7)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (132)) (Prims.of_int (12))
                               (Prims.of_int (132)) (Prims.of_int (84)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (132)) (Prims.of_int (6))
                               (Prims.of_int (132)) (Prims.of_int (84)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (132)) (Prims.of_int (43))
                                     (Prims.of_int (132)) (Prims.of_int (83)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (132)) (Prims.of_int (12))
                                     (Prims.of_int (132)) (Prims.of_int (84)))))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (132))
                                           (Prims.of_int (43))
                                           (Prims.of_int (132))
                                           (Prims.of_int (61)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (132))
                                           (Prims.of_int (43))
                                           (Prims.of_int (132))
                                           (Prims.of_int (83)))))
                                  (Obj.magic (term_to_doc inames))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (132))
                                                      (Prims.of_int (66))
                                                      (Prims.of_int (132))
                                                      (Prims.of_int (83)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (132))
                                                      (Prims.of_int (43))
                                                      (Prims.of_int (132))
                                                      (Prims.of_int (83)))))
                                             (Obj.magic
                                                (term_to_doc
                                                   s.Pulse_Syntax_Base.res))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     FStar_Pprint.op_Hat_Slash_Hat
                                                       uu___ uu___1)))) uu___)))
                            (fun uu___ ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    FStar_Pprint.op_Hat_Slash_Hat
                                      (FStar_Pprint.doc_of_string "stt_ghost")
                                      uu___))))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> FStar_Pprint.group uu___))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (133)) (Prims.of_int (10))
                                    (Prims.of_int (134)) (Prims.of_int (82)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (131)) (Prims.of_int (13))
                                    (Prims.of_int (135)) (Prims.of_int (7)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (133))
                                          (Prims.of_int (10))
                                          (Prims.of_int (133))
                                          (Prims.of_int (82)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (133))
                                          (Prims.of_int (10))
                                          (Prims.of_int (134))
                                          (Prims.of_int (82)))))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (133))
                                                (Prims.of_int (17))
                                                (Prims.of_int (133))
                                                (Prims.of_int (82)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (133))
                                                (Prims.of_int (10))
                                                (Prims.of_int (133))
                                                (Prims.of_int (82)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (133))
                                                      (Prims.of_int (24))
                                                      (Prims.of_int (133))
                                                      (Prims.of_int (81)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (133))
                                                      (Prims.of_int (17))
                                                      (Prims.of_int (133))
                                                      (Prims.of_int (82)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Syntax.Printer.fst"
                                                            (Prims.of_int (133))
                                                            (Prims.of_int (32))
                                                            (Prims.of_int (133))
                                                            (Prims.of_int (80)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Syntax.Printer.fst"
                                                            (Prims.of_int (133))
                                                            (Prims.of_int (24))
                                                            (Prims.of_int (133))
                                                            (Prims.of_int (81)))))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Syntax.Printer.fst"
                                                                  (Prims.of_int (133))
                                                                  (Prims.of_int (62))
                                                                  (Prims.of_int (133))
                                                                  (Prims.of_int (79)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Syntax.Printer.fst"
                                                                  (Prims.of_int (133))
                                                                  (Prims.of_int (32))
                                                                  (Prims.of_int (133))
                                                                  (Prims.of_int (80)))))
                                                         (Obj.magic
                                                            (term_to_doc
                                                               s.Pulse_Syntax_Base.pre))
                                                         (fun uu___1 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 FStar_Pprint.op_Hat_Slash_Hat
                                                                   (FStar_Pprint.doc_of_string
                                                                    "requires")
                                                                   uu___1))))
                                                   (fun uu___1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           FStar_Pprint.parens
                                                             uu___1))))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     FStar_Pprint.group
                                                       uu___1))))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               FStar_Pprint.nest
                                                 (Prims.of_int (2)) uu___1))))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (134))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (134))
                                                     (Prims.of_int (82)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (133))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (134))
                                                     (Prims.of_int (82)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (134))
                                                           (Prims.of_int (17))
                                                           (Prims.of_int (134))
                                                           (Prims.of_int (82)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (134))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (134))
                                                           (Prims.of_int (82)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (134))
                                                                 (Prims.of_int (24))
                                                                 (Prims.of_int (134))
                                                                 (Prims.of_int (81)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (134))
                                                                 (Prims.of_int (17))
                                                                 (Prims.of_int (134))
                                                                 (Prims.of_int (82)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (80)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (81)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (79)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (80)))))
                                                                    (
                                                                    Obj.magic
                                                                    (term_to_doc
                                                                    s.Pulse_Syntax_Base.post))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (FStar_Pprint.doc_of_string
                                                                    "ensures")
                                                                    uu___2))))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.parens
                                                                    uu___2))))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                FStar_Pprint.group
                                                                  uu___2))))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          FStar_Pprint.nest
                                                            (Prims.of_int (2))
                                                            uu___2))))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                      uu___1 uu___2))))
                                      uu___1)))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1))))
                     uu___)))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_Pprint.nest (Prims.of_int (2)) uu___))
let (comp_to_string :
  Pulse_Syntax_Base.comp ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun c ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (137)) (Prims.of_int (30)) (Prims.of_int (137))
               (Prims.of_int (45)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (137)) (Prims.of_int (23)) (Prims.of_int (137))
               (Prims.of_int (45))))) (Obj.magic (comp_to_doc c))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_Pprint.render uu___))
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
                 (Prims.of_int (147)) (Prims.of_int (22))
                 (Prims.of_int (147)) (Prims.of_int (46)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                 (Prims.of_int (147)) (Prims.of_int (4)) (Prims.of_int (147))
                 (Prims.of_int (46)))))
        (Obj.magic (FStar_Tactics_Util.map term_to_string t))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStar_String.concat sep uu___))
let separate_map :
  'a .
    FStar_Pprint.document ->
      ('a -> (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr) ->
        'a Prims.list ->
          (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr
  =
  fun sep ->
    fun f ->
      fun l ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (151)) (Prims.of_int (15))
                   (Prims.of_int (151)) (Prims.of_int (26)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (151)) (Prims.of_int (2))
                   (Prims.of_int (151)) (Prims.of_int (26)))))
          (Obj.magic (FStar_Tactics_Util.map f l))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_Pprint.separate sep uu___))
let (braced : FStar_Pprint.document -> FStar_Pprint.document) =
  fun d ->
    FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
      (FStar_Pprint.doc_of_string "{") d (FStar_Pprint.doc_of_string "}")
let rec (st_term_to_doc :
  Pulse_Syntax_Base.st_term ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
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
                   (Prims.of_int (160)) (Prims.of_int (12))
                   (Prims.of_int (167)) (Prims.of_int (29)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (160)) (Prims.of_int (6))
                   (Prims.of_int (167)) (Prims.of_int (29)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (167)) (Prims.of_int (12))
                         (Prims.of_int (167)) (Prims.of_int (28)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (160)) (Prims.of_int (12))
                         (Prims.of_int (167)) (Prims.of_int (29)))))
                (Obj.magic (term_to_doc term))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        FStar_Pprint.op_Hat_Slash_Hat
                          (FStar_Pprint.doc_of_string
                             (Prims.strcat
                                (Prims.strcat "return_"
                                   (Prims.strcat
                                      (match ctag with
                                       | Pulse_Syntax_Base.STT -> "stt"
                                       | Pulse_Syntax_Base.STT_Atomic ->
                                           "stt_atomic"
                                       | Pulse_Syntax_Base.STT_Ghost ->
                                           "stt_ghost") ""))
                                (Prims.strcat
                                   (if insert_eq then "" else "_noeq") "")))
                          uu___))))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_Pprint.group uu___))
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = head;
          Pulse_Syntax_Base.arg_qual = arg_qual;
          Pulse_Syntax_Base.arg = arg;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (170)) (Prims.of_int (13))
                   (Prims.of_int (174)) (Prims.of_int (7)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (170)) (Prims.of_int (6))
                   (Prims.of_int (174)) (Prims.of_int (7)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (172)) (Prims.of_int (12))
                         (Prims.of_int (173)) (Prims.of_int (51)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (170)) (Prims.of_int (13))
                         (Prims.of_int (174)) (Prims.of_int (7)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (172)) (Prims.of_int (12))
                               (Prims.of_int (172)) (Prims.of_int (28)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (172)) (Prims.of_int (12))
                               (Prims.of_int (173)) (Prims.of_int (51)))))
                      (Obj.magic (term_to_doc head))
                      (fun uu___ ->
                         (fun uu___ ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (173))
                                          (Prims.of_int (12))
                                          (Prims.of_int (173))
                                          (Prims.of_int (51)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (172))
                                          (Prims.of_int (12))
                                          (Prims.of_int (173))
                                          (Prims.of_int (51)))))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (173))
                                                (Prims.of_int (36))
                                                (Prims.of_int (173))
                                                (Prims.of_int (51)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (173))
                                                (Prims.of_int (12))
                                                (Prims.of_int (173))
                                                (Prims.of_int (51)))))
                                       (Obj.magic (term_to_doc arg))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               FStar_Pprint.op_Hat_Hat
                                                 (qual_to_doc arg_qual)
                                                 uu___1))))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         FStar_Pprint.op_Hat_Slash_Hat uu___
                                           uu___1)))) uu___)))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        FStar_Pprint.op_Hat_Slash_Hat
                          (if dbg_printing
                           then FStar_Pprint.doc_of_string "<stapp>"
                           else FStar_Pprint.empty) uu___))))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_Pprint.parens uu___))
    | Pulse_Syntax_Base.Tm_Bind
        { Pulse_Syntax_Base.binder = binder; Pulse_Syntax_Base.head1 = head;
          Pulse_Syntax_Base.body1 = body;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (177)) (Prims.of_int (6))
                   (Prims.of_int (180)) (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (177)) (Prims.of_int (6))
                   (Prims.of_int (181)) (Prims.of_int (29)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (178)) (Prims.of_int (8))
                         (Prims.of_int (178)) (Prims.of_int (95)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (177)) (Prims.of_int (6))
                         (Prims.of_int (180)) (Prims.of_int (28)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (178)) (Prims.of_int (15))
                               (Prims.of_int (178)) (Prims.of_int (94)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (178)) (Prims.of_int (8))
                               (Prims.of_int (178)) (Prims.of_int (95)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (178)) (Prims.of_int (51))
                                     (Prims.of_int (178)) (Prims.of_int (73)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (178)) (Prims.of_int (15))
                                     (Prims.of_int (178)) (Prims.of_int (94)))))
                            (Obj.magic (binder_to_doc binder))
                            (fun uu___ ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    FStar_Pprint.surround (Prims.of_int (2))
                                      Prims.int_one
                                      (FStar_Pprint.doc_of_string "let")
                                      uu___ (FStar_Pprint.doc_of_string "=")))))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> FStar_Pprint.group uu___))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (179)) (Prims.of_int (8))
                                    (Prims.of_int (179)) (Prims.of_int (29)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (177)) (Prims.of_int (6))
                                    (Prims.of_int (180)) (Prims.of_int (28)))))
                           (Obj.magic (st_term_to_doc head))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Pprint.surround (Prims.of_int (2))
                                     Prims.int_one uu___ uu___1
                                     (FStar_Pprint.doc_of_string "in")))))
                     uu___)))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (181)) (Prims.of_int (10))
                              (Prims.of_int (181)) (Prims.of_int (29)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (177)) (Prims.of_int (6))
                              (Prims.of_int (181)) (Prims.of_int (29)))))
                     (Obj.magic (st_term_to_doc body))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1))))
               uu___)
    | Pulse_Syntax_Base.Tm_TotBind
        { Pulse_Syntax_Base.binder1 = binder; Pulse_Syntax_Base.head2 = head;
          Pulse_Syntax_Base.body2 = body;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (184)) (Prims.of_int (6))
                   (Prims.of_int (187)) (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (184)) (Prims.of_int (6))
                   (Prims.of_int (188)) (Prims.of_int (29)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (185)) (Prims.of_int (8))
                         (Prims.of_int (185)) (Prims.of_int (99)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (184)) (Prims.of_int (6))
                         (Prims.of_int (187)) (Prims.of_int (28)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (185)) (Prims.of_int (15))
                               (Prims.of_int (185)) (Prims.of_int (98)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (185)) (Prims.of_int (8))
                               (Prims.of_int (185)) (Prims.of_int (99)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (185)) (Prims.of_int (55))
                                     (Prims.of_int (185)) (Prims.of_int (77)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (185)) (Prims.of_int (15))
                                     (Prims.of_int (185)) (Prims.of_int (98)))))
                            (Obj.magic (binder_to_doc binder))
                            (fun uu___ ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    FStar_Pprint.surround (Prims.of_int (2))
                                      Prims.int_one
                                      (FStar_Pprint.doc_of_string "let tot")
                                      uu___ (FStar_Pprint.doc_of_string "=")))))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> FStar_Pprint.group uu___))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (186)) (Prims.of_int (8))
                                    (Prims.of_int (186)) (Prims.of_int (26)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (184)) (Prims.of_int (6))
                                    (Prims.of_int (187)) (Prims.of_int (28)))))
                           (Obj.magic (term_to_doc head))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Pprint.surround (Prims.of_int (2))
                                     Prims.int_one uu___ uu___1
                                     (FStar_Pprint.doc_of_string "in")))))
                     uu___)))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (188)) (Prims.of_int (10))
                              (Prims.of_int (188)) (Prims.of_int (29)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (184)) (Prims.of_int (6))
                              (Prims.of_int (188)) (Prims.of_int (29)))))
                     (Obj.magic (st_term_to_doc body))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1))))
               uu___)
    | Pulse_Syntax_Base.Tm_Abs
        { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
          Pulse_Syntax_Base.ascription = c; Pulse_Syntax_Base.body = body;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (191)) (Prims.of_int (6))
                   (Prims.of_int (191)) (Prims.of_int (79)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (191)) (Prims.of_int (6))
                   (Prims.of_int (192)) (Prims.of_int (38)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (191)) (Prims.of_int (12))
                         (Prims.of_int (191)) (Prims.of_int (79)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (191)) (Prims.of_int (6))
                         (Prims.of_int (191)) (Prims.of_int (79)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (191)) (Prims.of_int (37))
                               (Prims.of_int (191)) (Prims.of_int (78)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (191)) (Prims.of_int (12))
                               (Prims.of_int (191)) (Prims.of_int (79)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (191)) (Prims.of_int (44))
                                     (Prims.of_int (191)) (Prims.of_int (78)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (191)) (Prims.of_int (37))
                                     (Prims.of_int (191)) (Prims.of_int (78)))))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (191))
                                           (Prims.of_int (62))
                                           (Prims.of_int (191))
                                           (Prims.of_int (77)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (191))
                                           (Prims.of_int (44))
                                           (Prims.of_int (191))
                                           (Prims.of_int (78)))))
                                  (Obj.magic (binder_to_doc b))
                                  (fun uu___ ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          FStar_Pprint.op_Hat_Hat
                                            (qual_to_doc q) uu___))))
                            (fun uu___ ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 -> FStar_Pprint.parens uu___))))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              FStar_Pprint.op_Hat_Slash_Hat
                                (FStar_Pprint.doc_of_string "fun") uu___))))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 -> FStar_Pprint.group uu___))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (192)) (Prims.of_int (10))
                              (Prims.of_int (192)) (Prims.of_int (38)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (191)) (Prims.of_int (6))
                              (Prims.of_int (192)) (Prims.of_int (38)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (192)) (Prims.of_int (17))
                                    (Prims.of_int (192)) (Prims.of_int (38)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (192)) (Prims.of_int (10))
                                    (Prims.of_int (192)) (Prims.of_int (38)))))
                           (Obj.magic (st_term_to_doc body))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> braced uu___1))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1))))
               uu___)
    | Pulse_Syntax_Base.Tm_If
        { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
          Pulse_Syntax_Base.else_ = else_; Pulse_Syntax_Base.post1 = uu___;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (195)) (Prims.of_int (6))
                   (Prims.of_int (195)) (Prims.of_int (63)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (195)) (Prims.of_int (6))
                   (Prims.of_int (198)) (Prims.of_int (39)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (195)) (Prims.of_int (39))
                         (Prims.of_int (195)) (Prims.of_int (63)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (195)) (Prims.of_int (6))
                         (Prims.of_int (195)) (Prims.of_int (63)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (195)) (Prims.of_int (47))
                               (Prims.of_int (195)) (Prims.of_int (62)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (195)) (Prims.of_int (39))
                               (Prims.of_int (195)) (Prims.of_int (63)))))
                      (Obj.magic (term_to_doc b))
                      (fun uu___1 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___2 -> FStar_Pprint.parens uu___1))))
                (fun uu___1 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                          (FStar_Pprint.doc_of_string "if") uu___1))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (196)) (Prims.of_int (10))
                              (Prims.of_int (198)) (Prims.of_int (39)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (195)) (Prims.of_int (6))
                              (Prims.of_int (198)) (Prims.of_int (39)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (196)) (Prims.of_int (10))
                                    (Prims.of_int (196)) (Prims.of_int (39)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (196)) (Prims.of_int (10))
                                    (Prims.of_int (198)) (Prims.of_int (39)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (196))
                                          (Prims.of_int (17))
                                          (Prims.of_int (196))
                                          (Prims.of_int (39)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (196))
                                          (Prims.of_int (10))
                                          (Prims.of_int (196))
                                          (Prims.of_int (39)))))
                                 (Obj.magic (st_term_to_doc then_))
                                 (fun uu___2 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 -> braced uu___2))))
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (197))
                                               (Prims.of_int (10))
                                               (Prims.of_int (198))
                                               (Prims.of_int (39)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (196))
                                               (Prims.of_int (10))
                                               (Prims.of_int (198))
                                               (Prims.of_int (39)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (198))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (198))
                                                     (Prims.of_int (39)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (197))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (198))
                                                     (Prims.of_int (39)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (198))
                                                           (Prims.of_int (17))
                                                           (Prims.of_int (198))
                                                           (Prims.of_int (39)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (198))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (198))
                                                           (Prims.of_int (39)))))
                                                  (Obj.magic
                                                     (st_term_to_doc else_))
                                                  (fun uu___3 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___4 ->
                                                          braced uu___3))))
                                            (fun uu___3 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___4 ->
                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                      (FStar_Pprint.doc_of_string
                                                         "else") uu___3))))
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              FStar_Pprint.op_Hat_Slash_Hat
                                                uu___2 uu___3)))) uu___2)))
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 ->
                             FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2))))
               uu___1)
    | Pulse_Syntax_Base.Tm_Match
        { Pulse_Syntax_Base.sc = sc; Pulse_Syntax_Base.returns_ = uu___;
          Pulse_Syntax_Base.brs = brs;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (201)) (Prims.of_int (6))
                   (Prims.of_int (201)) (Prims.of_int (91)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (201)) (Prims.of_int (6))
                   (Prims.of_int (202)) (Prims.of_int (38)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (201)) (Prims.of_int (43))
                         (Prims.of_int (201)) (Prims.of_int (68)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (201)) (Prims.of_int (6))
                         (Prims.of_int (201)) (Prims.of_int (91)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (201)) (Prims.of_int (51))
                               (Prims.of_int (201)) (Prims.of_int (67)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (201)) (Prims.of_int (43))
                               (Prims.of_int (201)) (Prims.of_int (68)))))
                      (Obj.magic (term_to_doc sc))
                      (fun uu___1 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___2 -> FStar_Pprint.parens uu___1))))
                (fun uu___1 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        FStar_Pprint.surround (Prims.of_int (2))
                          Prims.int_one (FStar_Pprint.doc_of_string "match")
                          uu___1 (FStar_Pprint.doc_of_string "with")))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (202)) (Prims.of_int (10))
                              (Prims.of_int (202)) (Prims.of_int (38)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (201)) (Prims.of_int (6))
                              (Prims.of_int (202)) (Prims.of_int (38)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (202)) (Prims.of_int (17))
                                    (Prims.of_int (202)) (Prims.of_int (38)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (202)) (Prims.of_int (10))
                                    (Prims.of_int (202)) (Prims.of_int (38)))))
                           (Obj.magic (branches_to_doc brs))
                           (fun uu___2 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 -> braced uu___2))))
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 ->
                             FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2))))
               uu___1)
    | Pulse_Syntax_Base.Tm_IntroPure { Pulse_Syntax_Base.p3 = p;_} ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (205)) (Prims.of_int (50))
                   (Prims.of_int (205)) (Prims.of_int (74)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (205)) (Prims.of_int (6))
                   (Prims.of_int (205)) (Prims.of_int (74)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (205)) (Prims.of_int (58))
                         (Prims.of_int (205)) (Prims.of_int (73)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (205)) (Prims.of_int (50))
                         (Prims.of_int (205)) (Prims.of_int (74)))))
                (Obj.magic (term_to_doc p))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 -> FStar_Pprint.parens uu___))))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                    (FStar_Pprint.doc_of_string "introduce pure") uu___))
    | Pulse_Syntax_Base.Tm_ElimExists { Pulse_Syntax_Base.p4 = p;_} ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (208)) (Prims.of_int (47))
                   (Prims.of_int (208)) (Prims.of_int (71)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (208)) (Prims.of_int (6))
                   (Prims.of_int (208)) (Prims.of_int (71)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (208)) (Prims.of_int (55))
                         (Prims.of_int (208)) (Prims.of_int (70)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (208)) (Prims.of_int (47))
                         (Prims.of_int (208)) (Prims.of_int (71)))))
                (Obj.magic (term_to_doc p))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 -> FStar_Pprint.parens uu___))))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                    (FStar_Pprint.doc_of_string "elim_exists") uu___))
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.p5 = p;
          Pulse_Syntax_Base.witnesses = witnesses;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (211)) (Prims.of_int (6))
                   (Prims.of_int (211)) (Prims.of_int (69)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (211)) (Prims.of_int (6))
                   (Prims.of_int (212)) (Prims.of_int (89)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (211)) (Prims.of_int (45))
                         (Prims.of_int (211)) (Prims.of_int (69)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (211)) (Prims.of_int (6))
                         (Prims.of_int (211)) (Prims.of_int (69)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (211)) (Prims.of_int (53))
                               (Prims.of_int (211)) (Prims.of_int (68)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (211)) (Prims.of_int (45))
                               (Prims.of_int (211)) (Prims.of_int (69)))))
                      (Obj.magic (term_to_doc p))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> FStar_Pprint.parens uu___))))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                          (FStar_Pprint.doc_of_string "introduce") uu___))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (212)) (Prims.of_int (10))
                              (Prims.of_int (212)) (Prims.of_int (89)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (211)) (Prims.of_int (6))
                              (Prims.of_int (212)) (Prims.of_int (89)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (212)) (Prims.of_int (35))
                                    (Prims.of_int (212)) (Prims.of_int (89)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (212)) (Prims.of_int (10))
                                    (Prims.of_int (212)) (Prims.of_int (89)))))
                           (Obj.magic
                              (separate_map (FStar_Pprint.doc_of_string " ")
                                 term_to_doc witnesses))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Pprint.op_Hat_Slash_Hat
                                     (FStar_Pprint.doc_of_string "with")
                                     uu___1))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1))))
               uu___)
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
                   (Prims.of_int (215)) (Prims.of_int (6))
                   (Prims.of_int (215)) (Prims.of_int (84)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (215)) (Prims.of_int (6))
                   (Prims.of_int (217)) (Prims.of_int (38)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (215)) (Prims.of_int (41))
                         (Prims.of_int (215)) (Prims.of_int (84)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (215)) (Prims.of_int (6))
                         (Prims.of_int (215)) (Prims.of_int (84)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (215)) (Prims.of_int (49))
                               (Prims.of_int (215)) (Prims.of_int (83)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (215)) (Prims.of_int (41))
                               (Prims.of_int (215)) (Prims.of_int (84)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (215)) (Prims.of_int (56))
                                     (Prims.of_int (215)) (Prims.of_int (82)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (215)) (Prims.of_int (49))
                                     (Prims.of_int (215)) (Prims.of_int (83)))))
                            (Obj.magic (st_term_to_doc condition))
                            (fun uu___1 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 -> FStar_Pprint.group uu___1))))
                      (fun uu___1 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___2 -> FStar_Pprint.parens uu___1))))
                (fun uu___1 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                          (FStar_Pprint.doc_of_string "while") uu___1))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (216)) (Prims.of_int (10))
                              (Prims.of_int (217)) (Prims.of_int (38)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (215)) (Prims.of_int (6))
                              (Prims.of_int (217)) (Prims.of_int (38)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (216)) (Prims.of_int (10))
                                    (Prims.of_int (216)) (Prims.of_int (81)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (216)) (Prims.of_int (10))
                                    (Prims.of_int (217)) (Prims.of_int (38)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (216))
                                          (Prims.of_int (17))
                                          (Prims.of_int (216))
                                          (Prims.of_int (81)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (216))
                                          (Prims.of_int (10))
                                          (Prims.of_int (216))
                                          (Prims.of_int (81)))))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (216))
                                                (Prims.of_int (57))
                                                (Prims.of_int (216))
                                                (Prims.of_int (80)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (216))
                                                (Prims.of_int (17))
                                                (Prims.of_int (216))
                                                (Prims.of_int (81)))))
                                       (Obj.magic (term_to_doc invariant))
                                       (fun uu___2 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___3 ->
                                               FStar_Pprint.prefix
                                                 (Prims.of_int (2))
                                                 Prims.int_one
                                                 (FStar_Pprint.doc_of_string
                                                    "invariant") uu___2))))
                                 (fun uu___2 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 ->
                                         FStar_Pprint.nest (Prims.of_int (2))
                                           uu___2))))
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (217))
                                               (Prims.of_int (10))
                                               (Prims.of_int (217))
                                               (Prims.of_int (38)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (216))
                                               (Prims.of_int (10))
                                               (Prims.of_int (217))
                                               (Prims.of_int (38)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (217))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (217))
                                                     (Prims.of_int (38)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (217))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (217))
                                                     (Prims.of_int (38)))))
                                            (Obj.magic (st_term_to_doc body))
                                            (fun uu___3 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___4 -> braced uu___3))))
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              FStar_Pprint.op_Hat_Slash_Hat
                                                uu___2 uu___3)))) uu___2)))
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 ->
                             FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2))))
               uu___1)
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
                   (Prims.of_int (221)) (Prims.of_int (10))
                   (Prims.of_int (226)) (Prims.of_int (45)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (220)) (Prims.of_int (6))
                   (Prims.of_int (226)) (Prims.of_int (45)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (221)) (Prims.of_int (10))
                         (Prims.of_int (223)) (Prims.of_int (45)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (221)) (Prims.of_int (10))
                         (Prims.of_int (226)) (Prims.of_int (45)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (221)) (Prims.of_int (17))
                               (Prims.of_int (223)) (Prims.of_int (45)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (221)) (Prims.of_int (10))
                               (Prims.of_int (223)) (Prims.of_int (45)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (221)) (Prims.of_int (18))
                                     (Prims.of_int (221)) (Prims.of_int (43)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (221)) (Prims.of_int (17))
                                     (Prims.of_int (223)) (Prims.of_int (45)))))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (221))
                                           (Prims.of_int (25))
                                           (Prims.of_int (221))
                                           (Prims.of_int (43)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (221))
                                           (Prims.of_int (18))
                                           (Prims.of_int (221))
                                           (Prims.of_int (43)))))
                                  (Obj.magic (term_to_doc pre1))
                                  (fun uu___ ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          FStar_Pprint.angles uu___))))
                            (fun uu___ ->
                               (fun uu___ ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (222))
                                                (Prims.of_int (18))
                                                (Prims.of_int (223))
                                                (Prims.of_int (44)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (221))
                                                (Prims.of_int (17))
                                                (Prims.of_int (223))
                                                (Prims.of_int (45)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (222))
                                                      (Prims.of_int (18))
                                                      (Prims.of_int (222))
                                                      (Prims.of_int (47)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (222))
                                                      (Prims.of_int (18))
                                                      (Prims.of_int (223))
                                                      (Prims.of_int (44)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Syntax.Printer.fst"
                                                            (Prims.of_int (222))
                                                            (Prims.of_int (25))
                                                            (Prims.of_int (222))
                                                            (Prims.of_int (47)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Syntax.Printer.fst"
                                                            (Prims.of_int (222))
                                                            (Prims.of_int (18))
                                                            (Prims.of_int (222))
                                                            (Prims.of_int (47)))))
                                                   (Obj.magic
                                                      (st_term_to_doc body1))
                                                   (fun uu___1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           FStar_Pprint.parens
                                                             uu___1))))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (223))
                                                                 (Prims.of_int (18))
                                                                 (Prims.of_int (223))
                                                                 (Prims.of_int (44)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (222))
                                                                 (Prims.of_int (18))
                                                                 (Prims.of_int (223))
                                                                 (Prims.of_int (44)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (44)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (44)))))
                                                              (Obj.magic
                                                                 (term_to_doc
                                                                    post1))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.angles
                                                                    uu___2))))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                FStar_Pprint.op_Hat_Slash_Hat
                                                                  uu___1
                                                                  uu___2))))
                                                  uu___1)))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               FStar_Pprint.op_Hat_Slash_Hat
                                                 uu___ uu___1)))) uu___)))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> FStar_Pprint.parens uu___))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (224)) (Prims.of_int (10))
                                    (Prims.of_int (226)) (Prims.of_int (45)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (221)) (Prims.of_int (10))
                                    (Prims.of_int (226)) (Prims.of_int (45)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (224))
                                          (Prims.of_int (17))
                                          (Prims.of_int (226))
                                          (Prims.of_int (45)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (224))
                                          (Prims.of_int (10))
                                          (Prims.of_int (226))
                                          (Prims.of_int (45)))))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (224))
                                                (Prims.of_int (18))
                                                (Prims.of_int (224))
                                                (Prims.of_int (43)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (224))
                                                (Prims.of_int (17))
                                                (Prims.of_int (226))
                                                (Prims.of_int (45)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (224))
                                                      (Prims.of_int (25))
                                                      (Prims.of_int (224))
                                                      (Prims.of_int (43)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (224))
                                                      (Prims.of_int (18))
                                                      (Prims.of_int (224))
                                                      (Prims.of_int (43)))))
                                             (Obj.magic (term_to_doc pre2))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     FStar_Pprint.angles
                                                       uu___1))))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (225))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (226))
                                                           (Prims.of_int (44)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (224))
                                                           (Prims.of_int (17))
                                                           (Prims.of_int (226))
                                                           (Prims.of_int (45)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (225))
                                                                 (Prims.of_int (18))
                                                                 (Prims.of_int (225))
                                                                 (Prims.of_int (47)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (225))
                                                                 (Prims.of_int (18))
                                                                 (Prims.of_int (226))
                                                                 (Prims.of_int (44)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (47)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (47)))))
                                                              (Obj.magic
                                                                 (st_term_to_doc
                                                                    body2))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.parens
                                                                    uu___2))))
                                                        (fun uu___2 ->
                                                           (fun uu___2 ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (44)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (44)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (term_to_doc
                                                                    post2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.angles
                                                                    uu___3))))
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___2
                                                                    uu___3))))
                                                             uu___2)))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          FStar_Pprint.op_Hat_Slash_Hat
                                                            uu___1 uu___2))))
                                            uu___1)))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         FStar_Pprint.parens uu___1))))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1))))
                     uu___)))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  FStar_Pprint.op_Hat_Slash_Hat
                    (FStar_Pprint.doc_of_string "par") uu___))
    | Pulse_Syntax_Base.Tm_Rewrite
        { Pulse_Syntax_Base.t11 = t1; Pulse_Syntax_Base.t21 = t2;_} ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (230)) (Prims.of_int (12))
                   (Prims.of_int (232)) (Prims.of_int (26)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (229)) (Prims.of_int (7))
                   (Prims.of_int (232)) (Prims.of_int (26)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (230)) (Prims.of_int (12))
                         (Prims.of_int (230)) (Prims.of_int (26)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (230)) (Prims.of_int (12))
                         (Prims.of_int (232)) (Prims.of_int (26)))))
                (Obj.magic (term_to_doc t1))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (231)) (Prims.of_int (12))
                                    (Prims.of_int (232)) (Prims.of_int (26)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (230)) (Prims.of_int (12))
                                    (Prims.of_int (232)) (Prims.of_int (26)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (232))
                                          (Prims.of_int (12))
                                          (Prims.of_int (232))
                                          (Prims.of_int (26)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (231))
                                          (Prims.of_int (12))
                                          (Prims.of_int (232))
                                          (Prims.of_int (26)))))
                                 (Obj.magic (term_to_doc t2))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         FStar_Pprint.op_Hat_Slash_Hat
                                           (FStar_Pprint.doc_of_string "as")
                                           uu___1))))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1))))
                     uu___)))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  FStar_Pprint.op_Hat_Slash_Hat
                    (FStar_Pprint.doc_of_string "rewrite") uu___))
    | Pulse_Syntax_Base.Tm_WithLocal
        { Pulse_Syntax_Base.binder2 = binder;
          Pulse_Syntax_Base.initializer1 = initializer1;
          Pulse_Syntax_Base.body4 = body;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (235)) (Prims.of_int (34))
                   (Prims.of_int (237)) (Prims.of_int (38)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (235)) (Prims.of_int (6))
                   (Prims.of_int (237)) (Prims.of_int (38)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (235)) (Prims.of_int (34))
                         (Prims.of_int (235)) (Prims.of_int (54)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (235)) (Prims.of_int (34))
                         (Prims.of_int (237)) (Prims.of_int (38)))))
                (Obj.magic (binder_to_doc binder))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (235)) (Prims.of_int (59))
                                    (Prims.of_int (237)) (Prims.of_int (38)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (235)) (Prims.of_int (34))
                                    (Prims.of_int (237)) (Prims.of_int (38)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (236))
                                          (Prims.of_int (10))
                                          (Prims.of_int (237))
                                          (Prims.of_int (38)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (235))
                                          (Prims.of_int (59))
                                          (Prims.of_int (237))
                                          (Prims.of_int (38)))))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (236))
                                                (Prims.of_int (10))
                                                (Prims.of_int (236))
                                                (Prims.of_int (33)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (236))
                                                (Prims.of_int (10))
                                                (Prims.of_int (237))
                                                (Prims.of_int (38)))))
                                       (Obj.magic (term_to_doc initializer1))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (236))
                                                           (Prims.of_int (38))
                                                           (Prims.of_int (237))
                                                           (Prims.of_int (38)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (236))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (237))
                                                           (Prims.of_int (38)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (237))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (237))
                                                                 (Prims.of_int (38)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (236))
                                                                 (Prims.of_int (38))
                                                                 (Prims.of_int (237))
                                                                 (Prims.of_int (38)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (38)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (38)))))
                                                              (Obj.magic
                                                                 (st_term_to_doc
                                                                    body))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.nest
                                                                    (Prims.of_int (2))
                                                                    uu___2))))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                FStar_Pprint.op_Hat_Slash_Hat
                                                                  (FStar_Pprint.doc_of_string
                                                                    "in")
                                                                  uu___2))))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          FStar_Pprint.op_Hat_Slash_Hat
                                                            uu___1 uu___2))))
                                            uu___1)))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         FStar_Pprint.op_Hat_Slash_Hat
                                           (FStar_Pprint.doc_of_string "=")
                                           uu___1))))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1))))
                     uu___)))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  FStar_Pprint.op_Hat_Slash_Hat
                    (FStar_Pprint.doc_of_string "let mut") uu___))
    | Pulse_Syntax_Base.Tm_WithLocalArray
        { Pulse_Syntax_Base.binder3 = binder;
          Pulse_Syntax_Base.initializer2 = initializer1;
          Pulse_Syntax_Base.length = length;
          Pulse_Syntax_Base.body5 = body;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (240)) (Prims.of_int (34))
                   (Prims.of_int (243)) (Prims.of_int (38)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (240)) (Prims.of_int (6))
                   (Prims.of_int (243)) (Prims.of_int (38)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (240)) (Prims.of_int (34))
                         (Prims.of_int (240)) (Prims.of_int (54)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (240)) (Prims.of_int (34))
                         (Prims.of_int (243)) (Prims.of_int (38)))))
                (Obj.magic (binder_to_doc binder))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (240)) (Prims.of_int (59))
                                    (Prims.of_int (243)) (Prims.of_int (38)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (240)) (Prims.of_int (34))
                                    (Prims.of_int (243)) (Prims.of_int (38)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (241))
                                          (Prims.of_int (10))
                                          (Prims.of_int (243))
                                          (Prims.of_int (38)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (240))
                                          (Prims.of_int (59))
                                          (Prims.of_int (243))
                                          (Prims.of_int (38)))))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (241))
                                                (Prims.of_int (10))
                                                (Prims.of_int (241))
                                                (Prims.of_int (89)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (241))
                                                (Prims.of_int (10))
                                                (Prims.of_int (243))
                                                (Prims.of_int (38)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (241))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (241))
                                                      (Prims.of_int (89)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (241))
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (241))
                                                      (Prims.of_int (89)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Syntax.Printer.fst"
                                                            (Prims.of_int (241))
                                                            (Prims.of_int (20))
                                                            (Prims.of_int (241))
                                                            (Prims.of_int (43)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Syntax.Printer.fst"
                                                            (Prims.of_int (241))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (241))
                                                            (Prims.of_int (89)))))
                                                   (Obj.magic
                                                      (term_to_doc
                                                         initializer1))
                                                   (fun uu___1 ->
                                                      (fun uu___1 ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (88)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (89)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (88)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (88)))))
                                                                    (
                                                                    Obj.magic
                                                                    (term_to_doc
                                                                    length))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (FStar_Pprint.doc_of_string
                                                                    ";")
                                                                    uu___2))))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___1
                                                                    uu___2))))
                                                        uu___1)))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     FStar_Pprint.brackets
                                                       uu___1))))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (242))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (243))
                                                           (Prims.of_int (38)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (241))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (243))
                                                           (Prims.of_int (38)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (243))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (243))
                                                                 (Prims.of_int (38)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (242))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (243))
                                                                 (Prims.of_int (38)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (38)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (38)))))
                                                              (Obj.magic
                                                                 (st_term_to_doc
                                                                    body))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.nest
                                                                    (Prims.of_int (2))
                                                                    uu___2))))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                FStar_Pprint.op_Hat_Slash_Hat
                                                                  (FStar_Pprint.doc_of_string
                                                                    "in")
                                                                  uu___2))))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          FStar_Pprint.op_Hat_Slash_Hat
                                                            uu___1 uu___2))))
                                            uu___1)))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         FStar_Pprint.op_Hat_Slash_Hat
                                           (FStar_Pprint.doc_of_string "=")
                                           uu___1))))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1))))
                     uu___)))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  FStar_Pprint.op_Hat_Slash_Hat
                    (FStar_Pprint.doc_of_string "let mut") uu___))
    | Pulse_Syntax_Base.Tm_Admit
        { Pulse_Syntax_Base.ctag1 = ctag; Pulse_Syntax_Base.u1 = u;
          Pulse_Syntax_Base.typ = typ; Pulse_Syntax_Base.post3 = post;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (250)) (Prims.of_int (10))
                   (Prims.of_int (254)) (Prims.of_int (43)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (246)) (Prims.of_int (6))
                   (Prims.of_int (254)) (Prims.of_int (43)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (251)) (Prims.of_int (10))
                         (Prims.of_int (254)) (Prims.of_int (43)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (250)) (Prims.of_int (10))
                         (Prims.of_int (254)) (Prims.of_int (43)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (251)) (Prims.of_int (10))
                               (Prims.of_int (251)) (Prims.of_int (25)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (251)) (Prims.of_int (10))
                               (Prims.of_int (254)) (Prims.of_int (43)))))
                      (Obj.magic (term_to_doc typ))
                      (fun uu___ ->
                         (fun uu___ ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (252))
                                          (Prims.of_int (10))
                                          (Prims.of_int (254))
                                          (Prims.of_int (43)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (251))
                                          (Prims.of_int (10))
                                          (Prims.of_int (254))
                                          (Prims.of_int (43)))))
                                 (match post with
                                  | FStar_Pervasives_Native.None ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 FStar_Pprint.empty)))
                                  | FStar_Pervasives_Native.Some post1 ->
                                      Obj.magic
                                        (Obj.repr (term_to_doc post1)))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         FStar_Pprint.op_Hat_Slash_Hat uu___
                                           uu___1)))) uu___)))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        FStar_Pprint.op_Hat_Slash_Hat
                          (FStar_Pprint.angles
                             (FStar_Pprint.doc_of_string
                                (universe_to_string Prims.int_zero u))) uu___))))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  FStar_Pprint.op_Hat_Slash_Hat
                    (FStar_Pprint.doc_of_string
                       (match ctag with
                        | Pulse_Syntax_Base.STT -> "stt_admit"
                        | Pulse_Syntax_Base.STT_Atomic -> "stt_atomic_admit"
                        | Pulse_Syntax_Base.STT_Ghost -> "stt_ghost_admit"))
                    uu___))
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders
        { Pulse_Syntax_Base.hint_type = hint_type;
          Pulse_Syntax_Base.binders = binders; Pulse_Syntax_Base.t3 = t1;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (258)) (Prims.of_int (8))
                   (Prims.of_int (260)) (Prims.of_int (114)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (261)) (Prims.of_int (8))
                   (Prims.of_int (283)) (Prims.of_int (54)))))
          (match binders with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pprint.empty)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (260)) (Prims.of_int (39))
                                (Prims.of_int (260)) (Prims.of_int (114)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (260)) (Prims.of_int (15))
                                (Prims.of_int (260)) (Prims.of_int (114)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (260))
                                      (Prims.of_int (39))
                                      (Prims.of_int (260))
                                      (Prims.of_int (93)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (260))
                                      (Prims.of_int (39))
                                      (Prims.of_int (260))
                                      (Prims.of_int (114)))))
                             (Obj.magic
                                (separate_map
                                   (FStar_Pprint.doc_of_string " ")
                                   binder_to_doc binders))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     FStar_Pprint.op_Hat_Hat uu___1
                                       (FStar_Pprint.doc_of_string ".")))))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStar_Pprint.op_Hat_Hat
                                 (FStar_Pprint.doc_of_string "with") uu___1)))))
          (fun uu___ ->
             (fun with_prefix ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (262)) (Prims.of_int (25))
                              (Prims.of_int (264)) (Prims.of_int (93)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (265)) (Prims.of_int (8))
                              (Prims.of_int (283)) (Prims.of_int (54)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           fun uu___ ->
                             (fun uu___ ->
                                fun uu___1 ->
                                  match uu___1 with
                                  | FStar_Pervasives_Native.None ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 FStar_Pprint.empty)))
                                  | FStar_Pervasives_Native.Some l ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (264))
                                                       (Prims.of_int (29))
                                                       (Prims.of_int (264))
                                                       (Prims.of_int (93)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (264))
                                                       (Prims.of_int (20))
                                                       (Prims.of_int (264))
                                                       (Prims.of_int (93)))))
                                              (Obj.magic
                                                 (separate_map
                                                    (FStar_Pprint.doc_of_string
                                                       "; ")
                                                    (fun uu___2 ->
                                                       (fun n ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  FStar_Pprint.doc_of_string
                                                                    n)))
                                                         uu___2) l))
                                              (fun uu___2 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 ->
                                                      FStar_Pprint.brackets
                                                        uu___2))))) uu___1
                               uu___))
                     (fun uu___ ->
                        (fun names_to_doc ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (267))
                                         (Prims.of_int (8))
                                         (Prims.of_int (281))
                                         (Prims.of_int (94)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (283))
                                         (Prims.of_int (6))
                                         (Prims.of_int (283))
                                         (Prims.of_int (54)))))
                                (match hint_type with
                                 | Pulse_Syntax_Base.ASSERT
                                     { Pulse_Syntax_Base.p = p;_} ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (269))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (269))
                                                   (Prims.of_int (51)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (269))
                                                   (Prims.of_int (11))
                                                   (Prims.of_int (269))
                                                   (Prims.of_int (51)))))
                                          (Obj.magic (term_to_doc p))
                                          (fun uu___ ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  FStar_Pprint.op_Hat_Slash_Hat
                                                    (FStar_Pprint.doc_of_string
                                                       "assert") uu___)))
                                 | Pulse_Syntax_Base.UNFOLD
                                     { Pulse_Syntax_Base.names1 = names;
                                       Pulse_Syntax_Base.p2 = p;_}
                                     ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (271))
                                                   (Prims.of_int (39))
                                                   (Prims.of_int (271))
                                                   (Prims.of_int (75)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (271))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (271))
                                                   (Prims.of_int (75)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (271))
                                                         (Prims.of_int (39))
                                                         (Prims.of_int (271))
                                                         (Prims.of_int (57)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (271))
                                                         (Prims.of_int (39))
                                                         (Prims.of_int (271))
                                                         (Prims.of_int (75)))))
                                                (Obj.magic
                                                   (names_to_doc names))
                                                (fun uu___ ->
                                                   (fun uu___ ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (75)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (75)))))
                                                           (Obj.magic
                                                              (term_to_doc p))
                                                           (fun uu___1 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___
                                                                    uu___1))))
                                                     uu___)))
                                          (fun uu___ ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  FStar_Pprint.op_Hat_Slash_Hat
                                                    (FStar_Pprint.doc_of_string
                                                       "unfold") uu___)))
                                 | Pulse_Syntax_Base.FOLD
                                     { Pulse_Syntax_Base.names = names;
                                       Pulse_Syntax_Base.p1 = p;_}
                                     ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (273))
                                                   (Prims.of_int (37))
                                                   (Prims.of_int (273))
                                                   (Prims.of_int (73)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (273))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (273))
                                                   (Prims.of_int (73)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (273))
                                                         (Prims.of_int (37))
                                                         (Prims.of_int (273))
                                                         (Prims.of_int (55)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (273))
                                                         (Prims.of_int (37))
                                                         (Prims.of_int (273))
                                                         (Prims.of_int (73)))))
                                                (Obj.magic
                                                   (names_to_doc names))
                                                (fun uu___ ->
                                                   (fun uu___ ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (73)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (73)))))
                                                           (Obj.magic
                                                              (term_to_doc p))
                                                           (fun uu___1 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___
                                                                    uu___1))))
                                                     uu___)))
                                          (fun uu___ ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  FStar_Pprint.op_Hat_Slash_Hat
                                                    (FStar_Pprint.doc_of_string
                                                       "fold") uu___)))
                                 | Pulse_Syntax_Base.RENAME
                                     { Pulse_Syntax_Base.pairs = pairs;
                                       Pulse_Syntax_Base.goal = goal;_}
                                     ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (276))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (279))
                                                   (Prims.of_int (66)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (275))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (279))
                                                   (Prims.of_int (66)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (276))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (276))
                                                         (Prims.of_int (122)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (276))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (279))
                                                         (Prims.of_int (66)))))
                                                (Obj.magic
                                                   (separate_map
                                                      (FStar_Pprint.doc_of_string
                                                         ", ")
                                                      (fun uu___ ->
                                                         match uu___ with
                                                         | (x, y) ->
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (74)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (115)))))
                                                               (Obj.magic
                                                                  (term_to_doc
                                                                    x))
                                                               (fun uu___1 ->
                                                                  (fun uu___1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (term_to_doc
                                                                    y))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (FStar_Pprint.doc_of_string
                                                                    "as")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___1
                                                                    uu___2))))
                                                                    uu___1))
                                                      pairs))
                                                (fun uu___ ->
                                                   (fun uu___ ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (66)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (66)))))
                                                           (match goal with
                                                            | FStar_Pervasives_Native.None
                                                                ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Pprint.empty)))
                                                            | FStar_Pervasives_Native.Some
                                                                t2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (term_to_doc
                                                                    t2))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (FStar_Pprint.doc_of_string
                                                                    "in")
                                                                    uu___1)))))
                                                           (fun uu___1 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___
                                                                    uu___1))))
                                                     uu___)))
                                          (fun uu___ ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  FStar_Pprint.op_Hat_Slash_Hat
                                                    (FStar_Pprint.doc_of_string
                                                       "rename each") uu___)))
                                 | Pulse_Syntax_Base.REWRITE
                                     { Pulse_Syntax_Base.t1 = t11;
                                       Pulse_Syntax_Base.t2 = t2;_}
                                     ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (281))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (281))
                                                   (Prims.of_int (94)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (281))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (281))
                                                   (Prims.of_int (94)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (281))
                                                         (Prims.of_int (38))
                                                         (Prims.of_int (281))
                                                         (Prims.of_int (52)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (281))
                                                         (Prims.of_int (38))
                                                         (Prims.of_int (281))
                                                         (Prims.of_int (94)))))
                                                (Obj.magic (term_to_doc t11))
                                                (fun uu___ ->
                                                   (fun uu___ ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (94)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (94)))))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (94)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (94)))))
                                                                 (Obj.magic
                                                                    (
                                                                    term_to_doc
                                                                    t2))
                                                                 (fun uu___1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (FStar_Pprint.doc_of_string
                                                                    "as")
                                                                    uu___1))))
                                                           (fun uu___1 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___
                                                                    uu___1))))
                                                     uu___)))
                                          (fun uu___ ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  FStar_Pprint.op_Hat_Slash_Hat
                                                    (FStar_Pprint.doc_of_string
                                                       "rewrite") uu___))))
                                (fun uu___ ->
                                   (fun doc ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (283))
                                                    (Prims.of_int (22))
                                                    (Prims.of_int (283))
                                                    (Prims.of_int (54)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (283))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (283))
                                                    (Prims.of_int (54)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (283))
                                                          (Prims.of_int (29))
                                                          (Prims.of_int (283))
                                                          (Prims.of_int (54)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (283))
                                                          (Prims.of_int (22))
                                                          (Prims.of_int (283))
                                                          (Prims.of_int (54)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (283))
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (283))
                                                                (Prims.of_int (54)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (283))
                                                                (Prims.of_int (29))
                                                                (Prims.of_int (283))
                                                                (Prims.of_int (54)))))
                                                       (Obj.magic
                                                          (st_term_to_doc t1))
                                                       (fun uu___ ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___1 ->
                                                               FStar_Pprint.op_Hat_Slash_Hat
                                                                 FStar_Pprint.semi
                                                                 uu___))))
                                                 (fun uu___ ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         FStar_Pprint.op_Hat_Hat
                                                           doc uu___))))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   FStar_Pprint.op_Hat_Slash_Hat
                                                     with_prefix uu___))))
                                     uu___))) uu___))) uu___)
and (branches_to_doc :
  (Pulse_Syntax_Base.pattern * Pulse_Syntax_Base.st_term) Prims.list ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun brs ->
       match brs with
       | [] ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.empty)))
       | b::bs ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (288)) (Prims.of_int (13))
                            (Prims.of_int (288)) (Prims.of_int (28)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (288)) (Prims.of_int (13))
                            (Prims.of_int (288)) (Prims.of_int (62)))))
                   (Obj.magic (branch_to_doc b))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (288))
                                       (Prims.of_int (32))
                                       (Prims.of_int (288))
                                       (Prims.of_int (62)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (288))
                                       (Prims.of_int (13))
                                       (Prims.of_int (288))
                                       (Prims.of_int (62)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Syntax.Printer.fst"
                                             (Prims.of_int (288))
                                             (Prims.of_int (44))
                                             (Prims.of_int (288))
                                             (Prims.of_int (62)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Syntax.Printer.fst"
                                             (Prims.of_int (288))
                                             (Prims.of_int (32))
                                             (Prims.of_int (288))
                                             (Prims.of_int (62)))))
                                    (Obj.magic (branches_to_doc bs))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            FStar_Pprint.op_Hat_Hat
                                              FStar_Pprint.hardline uu___1))))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      FStar_Pprint.op_Hat_Hat uu___ uu___1))))
                        uu___)))) uu___
and (branch_to_doc :
  Pulse_Syntax_Base.branch ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun br ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (291)) (Prims.of_int (17)) (Prims.of_int (291))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (290)) (Prims.of_int (48)) (Prims.of_int (295))
               (Prims.of_int (34)))))
      (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> br))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (pat, e) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (292)) (Prims.of_int (9))
                              (Prims.of_int (295)) (Prims.of_int (34)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (292)) (Prims.of_int (2))
                              (Prims.of_int (295)) (Prims.of_int (34)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (293)) (Prims.of_int (4))
                                    (Prims.of_int (293)) (Prims.of_int (22)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (292)) (Prims.of_int (9))
                                    (Prims.of_int (295)) (Prims.of_int (34)))))
                           (Obj.magic (pattern_to_doc pat))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (294))
                                               (Prims.of_int (8))
                                               (Prims.of_int (295))
                                               (Prims.of_int (33)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (292))
                                               (Prims.of_int (9))
                                               (Prims.of_int (295))
                                               (Prims.of_int (34)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (295))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (295))
                                                     (Prims.of_int (33)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (294))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (295))
                                                     (Prims.of_int (33)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (295))
                                                           (Prims.of_int (15))
                                                           (Prims.of_int (295))
                                                           (Prims.of_int (33)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (295))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (295))
                                                           (Prims.of_int (33)))))
                                                  (Obj.magic
                                                     (st_term_to_doc e))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          FStar_Pprint.nest
                                                            (Prims.of_int (2))
                                                            uu___2))))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                      (FStar_Pprint.doc_of_string
                                                         "->") uu___2))))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 ->
                                              FStar_Pprint.op_Hat_Slash_Hat
                                                uu___1 uu___2)))) uu___1)))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> braced uu___1)))) uu___)
and (pattern_to_doc :
  Pulse_Syntax_Base.pattern ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun p ->
       match p with
       | Pulse_Syntax_Base.Pat_Cons (fv, pats) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (301)) (Prims.of_int (8))
                            (Prims.of_int (301)) (Prims.of_int (78)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (300)) (Prims.of_int (4))
                            (Prims.of_int (301)) (Prims.of_int (78)))))
                   (Obj.magic
                      (separate_map (FStar_Pprint.doc_of_string " ")
                         (fun uu___ ->
                            match uu___ with
                            | (p1, uu___1) -> pattern_to_doc p1) pats))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           FStar_Pprint.op_Hat_Slash_Hat
                             (FStar_Pprint.doc_of_string
                                (FStar_String.concat "."
                                   fv.Pulse_Syntax_Base.fv_name)) uu___))))
       | Pulse_Syntax_Base.Pat_Constant c ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "<constant>")))
       | Pulse_Syntax_Base.Pat_Var (x, uu___) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (305)) (Prims.of_int (18))
                            (Prims.of_int (305)) (Prims.of_int (30)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (305)) (Prims.of_int (4))
                            (Prims.of_int (305)) (Prims.of_int (30)))))
                   (Obj.magic (FStar_Tactics_Unseal.unseal x))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> FStar_Pprint.doc_of_string uu___1))))
       | Pulse_Syntax_Base.Pat_Dot_Term (FStar_Pervasives_Native.None) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.empty)))
       | Pulse_Syntax_Base.Pat_Dot_Term (FStar_Pervasives_Native.Some t) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "(.??)")))) uu___
let (pattern_to_string :
  Pulse_Syntax_Base.pattern ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (311)) (Prims.of_int (33)) (Prims.of_int (311))
               (Prims.of_int (51)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (311)) (Prims.of_int (26)) (Prims.of_int (311))
               (Prims.of_int (51))))) (Obj.magic (pattern_to_doc p))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_Pprint.render uu___))
let (st_term_to_string :
  Pulse_Syntax_Base.st_term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (312)) (Prims.of_int (33)) (Prims.of_int (312))
               (Prims.of_int (51)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (312)) (Prims.of_int (26)) (Prims.of_int (312))
               (Prims.of_int (51))))) (Obj.magic (st_term_to_doc t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_Pprint.render uu___))
let (tag_of_term : Pulse_Syntax_Base.term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_Emp -> "Tm_Emp"
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
    | Pulse_Syntax_Base.Tm_WithLocalArray uu___ -> "Tm_WithLocalArray"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Tm_Rewrite"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Tm_Admit"
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___ ->
        "Tm_ProofHintWithBinders"
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
                            (Prims.of_int (352)) (Prims.of_int (31))
                            (Prims.of_int (352)) (Prims.of_int (49)))))
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
                            (Prims.of_int (354)) (Prims.of_int (30))
                            (Prims.of_int (354)) (Prims.of_int (48)))))
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
    | Pulse_Syntax_Base.Tm_WithLocalArray uu___ -> "WithLocalArray"
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = p; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_IntroPure uu___ -> "IntroPure"
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "IntroExists"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "ElimExists"
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___ -> "AssertWithBinders"
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
    | Pulse_Syntax_Base.Tm_WithLocalArray uu___ -> "WithLocalArray"
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = p; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_IntroPure uu___ -> "IntroPure"
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "IntroExists"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "ElimExists"
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___ -> "AssertWithBinders"
let (decl_to_string :
  Pulse_Syntax_Base.decl ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    match d.Pulse_Syntax_Base.d with
    | Pulse_Syntax_Base.FnDecl
        { Pulse_Syntax_Base.id = id; Pulse_Syntax_Base.isrec = isrec;
          Pulse_Syntax_Base.bs = uu___; Pulse_Syntax_Base.comp = uu___1;
          Pulse_Syntax_Base.meas = uu___2; Pulse_Syntax_Base.body6 = body;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (407)) (Prims.of_int (13))
                   (Prims.of_int (407)) (Prims.of_int (109)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                   (Prims.of_int (19)) (Prims.of_int (590))
                   (Prims.of_int (31)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (407)) (Prims.of_int (46))
                         (Prims.of_int (407)) (Prims.of_int (109)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                         (Prims.of_int (19)) (Prims.of_int (590))
                         (Prims.of_int (31)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (407)) (Prims.of_int (73))
                               (Prims.of_int (407)) (Prims.of_int (109)))))
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
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (407)) (Prims.of_int (81))
                                     (Prims.of_int (407))
                                     (Prims.of_int (109)))))
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
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (407))
                                           (Prims.of_int (81))
                                           (Prims.of_int (407))
                                           (Prims.of_int (103)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "prims.fst"
                                           (Prims.of_int (590))
                                           (Prims.of_int (19))
                                           (Prims.of_int (590))
                                           (Prims.of_int (31)))))
                                  (Obj.magic (st_term_to_string body))
                                  (fun uu___3 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 -> Prims.strcat uu___3 "}"))))
                            (fun uu___3 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___4 -> Prims.strcat " { " uu___3))))
                      (fun uu___3 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___4 ->
                              Prims.strcat
                                (FStar_Pervasives_Native.fst
                                   (FStar_Reflection_V2_Builtins.inspect_ident
                                      id)) uu___3))))
                (fun uu___3 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___4 ->
                        Prims.strcat (if isrec then "rec " else "") uu___3))))
          (fun uu___3 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___4 -> Prims.strcat "let " uu___3))