module L0Core
open Pulse.Main
open Pulse.Steel.Wrapper
open Pulse.Class.BoundedIntegers
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
module R = Steel.ST.Reference
module A = Steel.ST.Array
module T = FStar.Tactics
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open L0Types
open L0Crypto
open X509
open HACL
open Array

(* l0 helpers *)

```pulse
fn create_deviceIDCRI
  (deviceID_pub: A.array U8.t)
  (deviceIDCRI_len: U32.t)
  (deviceIDCRI_buf: A.array U8.t)
  (deviceIDCSR_ingredients: deviceIDCSR_ingredients_t)
  (#pub_perm:perm)
  (#pub#_buf:erased (Seq.seq U8.t))
  requires 
    A.pts_to deviceID_pub pub_perm pub **
    A.pts_to deviceIDCRI_buf full_perm _buf **
    pure (
      deviceIDCRI_len == len_of_deviceIDCRI 
                          deviceIDCSR_ingredients.version
                          deviceIDCSR_ingredients.s_common
                          deviceIDCSR_ingredients.s_org
                          deviceIDCSR_ingredients.s_country
    )
  ensures
    exists (buf:Seq.seq U8.t).
      A.pts_to deviceID_pub pub_perm pub **
      A.pts_to deviceIDCRI_buf full_perm buf **
      pure (
        buf `Seq.equal`
          (spec_serialize_deviceIDCRI 
            (spec_x509_get_deviceIDCRI
              deviceIDCSR_ingredients.version
              deviceIDCSR_ingredients.s_common
              deviceIDCSR_ingredients.s_org
              deviceIDCSR_ingredients.s_country
              deviceIDCSR_ingredients.ku
              pub) 
            deviceIDCRI_len)
      )
{
  let deviceIDCRI = x509_get_deviceIDCRI
                      deviceIDCSR_ingredients.version
                      deviceIDCSR_ingredients.s_common
                      deviceIDCSR_ingredients.s_org
                      deviceIDCSR_ingredients.s_country
                      deviceIDCSR_ingredients.ku
                      deviceID_pub;
  serialize_deviceIDCRI deviceIDCRI deviceIDCRI_len deviceIDCRI_buf;
  ()
}
```

// TODO: don't need full perm on all of these
```pulse
fn sign_and_finalize_deviceIDCSR
  (deviceID_priv: A.array U8.t)
  (deviceIDCRI_len: U32.t)
  (deviceIDCRI_buf: A.array U8.t)
  (deviceIDCSR_len: U32.t)
  (deviceIDCSR_buf: A.array U8.t)
  (deviceIDCSR_ingredients: deviceIDCSR_ingredients_t)
  (#priv_perm:perm)
  (#priv#_cri_buf#_csr_buf:erased (Seq.seq U8.t))
  requires (
    A.pts_to deviceID_priv priv_perm priv **
    A.pts_to deviceIDCRI_buf full_perm _cri_buf **
    A.pts_to deviceIDCSR_buf full_perm _csr_buf **
    pure (
      deviceIDCRI_len == len_of_deviceIDCRI 
                          deviceIDCSR_ingredients.version
                          deviceIDCSR_ingredients.s_common
                          deviceIDCSR_ingredients.s_org
                          deviceIDCSR_ingredients.s_country /\
      0 < U32.v deviceIDCRI_len /\ 
      valid_deviceIDCSR_ingredients deviceIDCRI_len /\
      deviceIDCSR_len == length_of_deviceIDCSR deviceIDCRI_len
    ))
  ensures (
    exists (csr_buf:Seq.seq U8.t). 
    A.pts_to deviceID_priv priv_perm priv **
    A.pts_to deviceIDCRI_buf full_perm _cri_buf **
    A.pts_to deviceIDCSR_buf full_perm csr_buf **
    pure (
      csr_buf `Seq.equal`
        (spec_serialize_deviceIDCSR 
          deviceIDCRI_len 
          deviceIDCSR_len
          (spec_x509_get_deviceIDCSR
            deviceIDCRI_len
            _cri_buf
            (spec_ed25519_sign
              priv
              _cri_buf)))
    ))
{
  let deviceIDCRI_sig = new_array 0uy (u32_to_us deviceIDCRI_len);

  ed25519_sign deviceIDCRI_sig deviceID_priv (u32_to_us deviceIDCRI_len) deviceIDCRI_buf;

  let deviceIDCSR = x509_get_deviceIDCSR
                      deviceIDCRI_len
                      deviceIDCRI_buf
                      deviceIDCRI_sig;
                    
  serialize_deviceIDCSR deviceIDCRI_len deviceIDCSR deviceIDCSR_buf deviceIDCSR_len;

  free_array deviceIDCRI_sig;
  ()
}
```

```pulse
fn create_aliasKeyTBS
  (fwid: A.larray U8.t 32)
  (authKeyID: A.array U8.t)
  (deviceID_pub: A.larray U8.t 32)
  (aliasKey_pub: A.larray U8.t 32)
  (aliasKeyTBS_len: U32.t)
  (aliasKeyTBS_buf: A.array U8.t)
  (aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t)
  (#fwid_perm #authKey_perm #device_perm #aliasKey_perm:perm)
  (#fwid0 #authKeyID0 #deviceID_pub0 #aliasKey_pub0 #_buf:erased (Seq.seq U8.t))
  requires 
    A.pts_to fwid fwid_perm fwid0 **
    A.pts_to authKeyID authKey_perm authKeyID0 **
    A.pts_to deviceID_pub device_perm deviceID_pub0 **
    A.pts_to aliasKey_pub aliasKey_perm aliasKey_pub0 **
    A.pts_to aliasKeyTBS_buf full_perm _buf ** 
    pure (
      aliasKeyTBS_len == len_of_aliasKeyTBS
                          aliasKeyCRT_ingredients.serialNumber
                          aliasKeyCRT_ingredients.i_common
                          aliasKeyCRT_ingredients.i_org
                          aliasKeyCRT_ingredients.i_country
                          aliasKeyCRT_ingredients.s_common
                          aliasKeyCRT_ingredients.s_org
                          aliasKeyCRT_ingredients.s_country
                          aliasKeyCRT_ingredients.l0_version
    )
  ensures exists (buf:Seq.seq U8.t).
    A.pts_to fwid fwid_perm fwid0 **
    A.pts_to authKeyID authKey_perm authKeyID0 **
    A.pts_to deviceID_pub device_perm deviceID_pub0 **
    A.pts_to aliasKey_pub aliasKey_perm aliasKey_pub0 **
    A.pts_to aliasKeyTBS_buf full_perm buf **
    pure (
      buf `Seq.equal`
        (spec_serialize_aliasKeyTBS 
          (spec_x509_get_aliasKeyTBS
            aliasKeyCRT_ingredients
            fwid0
            deviceID_pub0
            aliasKey_pub0) 
          aliasKeyTBS_len)
    )
{
  let aliasKeyTBS = x509_get_aliasKeyTBS
                      aliasKeyCRT_ingredients
                      fwid
                      deviceID_pub
                      aliasKey_pub;

  serialize_aliasKeyTBS aliasKeyTBS aliasKeyTBS_len aliasKeyTBS_buf;
  ()
}
```

// TODO: don't need full perm on all of these
```pulse
fn sign_and_finalize_aliasKeyCRT
  (deviceID_priv: A.array U8.t)
  (aliasKeyTBS_len: U32.t)
  (aliasKeyTBS_buf: A.array U8.t)
  (aliasKeyCRT_len: U32.t)
  (aliasKeyCRT_buf: A.array U8.t)
  (aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t)
  (#priv_perm:perm)
  (#priv#_tbs_buf#_crt_buf:erased (Seq.seq U8.t))
  requires (
    A.pts_to deviceID_priv priv_perm priv **
    A.pts_to aliasKeyTBS_buf full_perm _tbs_buf **
    A.pts_to aliasKeyCRT_buf full_perm _crt_buf **
    pure (
      aliasKeyTBS_len == len_of_aliasKeyTBS
                          aliasKeyCRT_ingredients.serialNumber
                          aliasKeyCRT_ingredients.i_common
                          aliasKeyCRT_ingredients.i_org
                          aliasKeyCRT_ingredients.i_country
                          aliasKeyCRT_ingredients.s_common
                          aliasKeyCRT_ingredients.s_org
                          aliasKeyCRT_ingredients.s_country
                          aliasKeyCRT_ingredients.l0_version /\
      0 < U32.v aliasKeyTBS_len /\ 
      valid_aliasKeyCRT_ingredients aliasKeyTBS_len /\
      aliasKeyCRT_len == length_of_aliasKeyCRT aliasKeyTBS_len
    ))
  ensures (
    exists (crt_buf:Seq.seq U8.t). 
    A.pts_to deviceID_priv priv_perm priv **
    A.pts_to aliasKeyTBS_buf full_perm _tbs_buf **
    A.pts_to aliasKeyCRT_buf full_perm crt_buf **
    pure (
      crt_buf `Seq.equal`
        (spec_serialize_aliasKeyCRT 
          aliasKeyTBS_len 
          aliasKeyCRT_len
          (spec_x509_get_aliasKeyCRT
            aliasKeyTBS_len
            _tbs_buf
            (spec_ed25519_sign
              priv
              _tbs_buf)))
    ))
{
  let aliasKeyTBS_sig = new_array 0uy (u32_to_us aliasKeyTBS_len);

  ed25519_sign aliasKeyTBS_sig deviceID_priv (u32_to_us aliasKeyTBS_len) aliasKeyTBS_buf;

  let aliasKeyCRT = x509_get_aliasKeyCRT
                      aliasKeyTBS_len
                      aliasKeyTBS_buf
                      aliasKeyTBS_sig;
                    
  serialize_aliasKeyCRT aliasKeyTBS_len aliasKeyCRT aliasKeyCRT_buf aliasKeyCRT_len;

  free_array aliasKeyTBS_sig;
  ()
}
```

(* pre / post conditions for l0 *)

let deviceIDCSR_pre 
  (deviceIDCSR: deviceIDCSR_ingredients_t) 
  (deviceIDCRI_len: U32.t) 
  (deviceIDCSR_len: U32.t) 
  : prop
  = deviceIDCRI_len == len_of_deviceIDCRI
                        deviceIDCSR.version
                        deviceIDCSR.s_common
                        deviceIDCSR.s_org
                        deviceIDCSR.s_country /\
    0 < U32.v deviceIDCRI_len /\ 
    valid_deviceIDCSR_ingredients deviceIDCRI_len /\
    deviceIDCSR_len == length_of_deviceIDCSR deviceIDCRI_len

let aliasKeyCRT_pre 
  (aliasKeyCRT:aliasKeyCRT_ingredients_t) 
  (aliasKeyTBS_len:U32.t) 
  (aliasKeyCRT_len:U32.t) 
  : prop
  = aliasKeyTBS_len == len_of_aliasKeyTBS
                        aliasKeyCRT.serialNumber
                        aliasKeyCRT.i_common
                        aliasKeyCRT.i_org
                        aliasKeyCRT.i_country
                        aliasKeyCRT.s_common
                        aliasKeyCRT.s_org
                        aliasKeyCRT.s_country
                        aliasKeyCRT.l0_version /\
    0 < U32.v aliasKeyTBS_len /\ 
    valid_aliasKeyCRT_ingredients aliasKeyTBS_len /\
    aliasKeyCRT_len == length_of_aliasKeyCRT aliasKeyTBS_len

let aliasKey_post 
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi:Seq.seq U8.t)
  (fwid:Seq.seq U8.t)
  (aliasKey_label_len:hkdf_lbl_len)
  (aliasKey_label:Seq.seq U8.t)
  (aliasKey_pub:Seq.seq U8.t)
  (aliasKey_priv:Seq.seq U8.t)
  : prop
  = (aliasKey_pub, aliasKey_priv) == derive_AliasKey_spec alg dig_len cdi fwid aliasKey_label_len aliasKey_label

let deviceIDCSR_post
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi: Seq.seq U8.t)
  (deviceID_label_len: hkdf_lbl_len)
  (deviceID_label: Seq.seq U8.t)
  (deviceIDCSR_ingredients: deviceIDCSR_ingredients_t)
  (deviceIDCSR_len: U32.t)
  (deviceIDCSR_buf: Seq.seq U8.t)
  : prop
  = let (deviceID_pub, deviceID_priv) = (derive_DeviceID_spec alg dig_len cdi deviceID_label_len deviceID_label) in 
    let deviceIDCRI_len = len_of_deviceIDCRI 
                            deviceIDCSR_ingredients.version
                            deviceIDCSR_ingredients.s_common
                            deviceIDCSR_ingredients.s_org
                            deviceIDCSR_ingredients.s_country in
      let deviceIDCRI_buf = spec_serialize_deviceIDCRI 
                              (spec_x509_get_deviceIDCRI
                                deviceIDCSR_ingredients.version
                                deviceIDCSR_ingredients.s_common
                                deviceIDCSR_ingredients.s_org
                                deviceIDCSR_ingredients.s_country
                                deviceIDCSR_ingredients.ku
                                deviceID_pub) 
                              deviceIDCRI_len in 
    deviceIDCSR_buf `Seq.equal`
      (spec_serialize_deviceIDCSR 
        deviceIDCRI_len 
        deviceIDCSR_len
        (spec_x509_get_deviceIDCSR
          deviceIDCRI_len
          deviceIDCRI_buf
          (spec_ed25519_sign
            deviceID_priv
            deviceIDCRI_buf)))

let aliasKeyCRT_post
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi:Seq.seq U8.t)
  (fwid:Seq.seq U8.t)
  (deviceID_label_len:hkdf_lbl_len)
  (deviceID_label:Seq.seq U8.t)
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (aliasKeyCRT_len:U32.t)
  (aliasKeyCRT_buf:Seq.seq U8.t)
  (aliasKey_pub:Seq.seq U8.t)
  : prop
  = let (deviceID_pub, deviceID_priv) = (derive_DeviceID_spec alg dig_len cdi deviceID_label_len deviceID_label) in 
    let authKeyID = derive_AuthKeyID_spec alg deviceID_pub in
    let aliasKeyTBS_len = len_of_aliasKeyTBS
                            aliasKeyCRT_ingredients.serialNumber
                            aliasKeyCRT_ingredients.i_common
                            aliasKeyCRT_ingredients.i_org
                            aliasKeyCRT_ingredients.i_country
                            aliasKeyCRT_ingredients.s_common
                            aliasKeyCRT_ingredients.s_org
                            aliasKeyCRT_ingredients.s_country
                            aliasKeyCRT_ingredients.l0_version in
    let aliasKeyTBS_buf = (spec_serialize_aliasKeyTBS 
                            (spec_x509_get_aliasKeyTBS
                              aliasKeyCRT_ingredients
                              fwid
                              deviceID_pub
                              aliasKey_pub) 
                            aliasKeyTBS_len) in
    aliasKeyCRT_buf `Seq.equal` 
      (spec_serialize_aliasKeyCRT 
        aliasKeyTBS_len 
        aliasKeyCRT_len
        (spec_x509_get_aliasKeyCRT
          aliasKeyTBS_len
          aliasKeyTBS_buf
          (spec_ed25519_sign
            deviceID_priv
            aliasKeyTBS_buf)))

```pulse
fn l0_main
  (cdi: A.larray U8.t (US.v dice_digest_len))
  (aliasKey_pub: A.larray U8.t 32)
  (aliasKey_priv: A.larray U8.t 32)
  (aliasKeyTBS_len:U32.t)
  (aliasKeyCRT_len:U32.t)
  (aliasKeyCRT: A.array U8.t)
  (deviceIDCRI_len:U32.t)
  (deviceIDCSR_len:U32.t)
  (deviceIDCSR: A.array U8.t)
  (record: l0_record_t)
  (#repr: Ghost.erased l0_record_repr)
  (#cdi0:Ghost.erased (elseq U8.t dice_digest_len))
  (#aliasKey_pub0 #aliasKey_priv0 #aliasKeyCRT0 #deviceIDCSR0: Ghost.erased (Seq.seq U8.t))
  requires (
    l0_record_perm record repr **
    A.pts_to cdi full_perm cdi0 **
    A.pts_to aliasKey_pub full_perm aliasKey_pub0 **
    A.pts_to aliasKey_priv full_perm aliasKey_priv0 **
    A.pts_to aliasKeyCRT full_perm aliasKeyCRT0 **
    A.pts_to deviceIDCSR full_perm deviceIDCSR0 **
    pure (
      deviceIDCSR_pre record.deviceIDCSR_ingredients deviceIDCRI_len deviceIDCSR_len /\
      aliasKeyCRT_pre record.aliasKeyCRT_ingredients aliasKeyTBS_len aliasKeyCRT_len /\
      valid_hkdf_ikm_len (digest_len dice_hash_alg)
    ))
  ensures (
      l0_record_perm record repr **
      A.pts_to cdi full_perm (Seq.create (US.v dice_digest_len) 0uy) **
      exists (aliasKey_pub1 aliasKey_priv1 aliasKeyCRT1 deviceIDCSR1:Seq.seq U8.t). (
        A.pts_to aliasKey_pub full_perm aliasKey_pub1 **
        A.pts_to aliasKey_priv full_perm aliasKey_priv1 **
        A.pts_to aliasKeyCRT full_perm aliasKeyCRT1 **
        A.pts_to deviceIDCSR full_perm deviceIDCSR1 **
        pure (
          valid_hkdf_ikm_len dice_digest_len /\
          aliasKey_post
            dice_hash_alg dice_digest_len cdi0 repr.fwid
            record.aliasKey_label_len repr.aliasKey_label 
            aliasKey_pub1 aliasKey_priv1 /\
          deviceIDCSR_post 
            dice_hash_alg dice_digest_len cdi0
            record.deviceID_label_len repr.deviceID_label record.deviceIDCSR_ingredients 
            deviceIDCSR_len deviceIDCSR1 /\       
          aliasKeyCRT_post 
            dice_hash_alg dice_digest_len cdi0 repr.fwid
            record.deviceID_label_len repr.deviceID_label record.aliasKeyCRT_ingredients 
            aliasKeyCRT_len aliasKeyCRT1 aliasKey_pub1
      )))
{
  unfold l0_record_perm record repr;

  let deviceID_pub = new_array 0uy 32sz;
  let deviceID_priv = new_array 0uy 32sz;
  derive_DeviceID dice_hash_alg 
    deviceID_pub deviceID_priv cdi 
    record.deviceID_label_len record.deviceID_label
    #(coerce dice_digest_len cdi0);

  derive_AliasKey dice_hash_alg
    aliasKey_pub aliasKey_priv cdi 
    record.fwid record.aliasKey_label_len record.aliasKey_label;
  
  let authKeyID = new_array 0uy dice_digest_len;
  derive_AuthKeyID dice_hash_alg
    authKeyID deviceID_pub;

  let deviceIDCRI = new_array 0uy (u32_to_us deviceIDCRI_len);
  create_deviceIDCRI deviceID_pub
    deviceIDCRI_len deviceIDCRI
    record.deviceIDCSR_ingredients;
  
  sign_and_finalize_deviceIDCSR deviceID_priv 
    deviceIDCRI_len deviceIDCRI
    deviceIDCSR_len deviceIDCSR
    record.deviceIDCSR_ingredients;

  let aliasKeyTBS = new_array 0uy (u32_to_us aliasKeyTBS_len);
  create_aliasKeyTBS record.fwid authKeyID
    deviceID_pub aliasKey_pub
    aliasKeyTBS_len aliasKeyTBS
    record.aliasKeyCRT_ingredients;

  sign_and_finalize_aliasKeyCRT deviceID_priv 
    aliasKeyTBS_len aliasKeyTBS
    aliasKeyCRT_len aliasKeyCRT
    record.aliasKeyCRT_ingredients;
  
  free_array deviceID_pub;
  free_array deviceID_priv;
  free_array authKeyID;
  free_array deviceIDCRI;
  free_array aliasKeyTBS;

  fold l0_record_perm record repr;

  zeroize_array dice_digest_len cdi #cdi0;
  ()
}
```