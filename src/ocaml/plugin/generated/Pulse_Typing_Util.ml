open Prims
let (check_equiv_now :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        (((unit, unit, unit) FStar_Tactics_Types.equiv_token
           FStar_Pervasives_Native.option * FStar_Tactics_Types.issues),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tcenv ->
    fun t0 ->
      fun t1 ->
        FStar_Tactics_V2_Derived.with_policy FStar_Tactics_Types.SMTSync
          (fun uu___ -> FStar_Tactics_V2_Builtins.check_equiv tcenv t0 t1)