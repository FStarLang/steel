module EngineCore
open Pulse.Main
open Pulse.Steel.Wrapper
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
module R = Steel.ST.Reference
module A = Steel.ST.Array
module T = FStar.Tactics
module US = FStar.SizeT
module U8 = FStar.UInt8
open Array
open CommonTypes
open EngineTypes
open HACL

assume
val drop (p:vprop)
    : stt unit p (fun _ -> emp)

assume
val stack_is_erased : vprop

let l0_is_authentic (repr:engine_record_repr) 
  : prop
  = spec_ed25519_verify 
      repr.l0_image_auth_pubkey 
      repr.l0_image_header 
      repr.l0_image_header_sig /\
    spec_hash dice_hash_alg repr.l0_binary == repr.l0_binary_hash

let cdi_functional_correctness (c0:Seq.seq U8.t) (repr:engine_record_repr)
  : prop 
  = c0 == spec_hmac dice_hash_alg (spec_hash dice_hash_alg uds_bytes) (spec_hash dice_hash_alg repr.l0_binary)

```pulse
fn authenticate_l0_image (record:engine_record_t) (#repr:Ghost.erased engine_record_repr)
    requires engine_record_perm record repr
    returns b:bool
    ensures (
        engine_record_perm record repr **
        pure (b ==> l0_is_authentic repr)
    )
{
  unfold engine_record_perm record repr;

  let valid_header_sig = ed25519_verify
                          record.l0_image_auth_pubkey
                          record.l0_image_header record.l0_image_header_size
                          record.l0_image_header_sig;
  
  let mut b = false;
  if valid_header_sig {
    let hash_buf = new_array 0uy dice_digest_len;
    hacl_hash dice_hash_alg record.l0_binary record.l0_binary_size hash_buf;
    let res = compare dice_digest_len hash_buf record.l0_binary_hash;
    free_array hash_buf;
    fold engine_record_perm record repr;
    res
  } else {
    fold engine_record_perm record repr;
    false
  };
}
```

```pulse
fn disable_uds (_:unit) 
    requires uds_is_enabled
    ensures emp
{
    drop uds_is_enabled
}
```

```pulse
fn zeroize_uds (uds:A.array U8.t) 
               (l:(l:US.t{ US.v l = A.length uds })) 
               (#uds0:(uds0:Ghost.erased (Seq.seq U8.t) { Seq.length uds0 = A.length uds }))
  requires (
    uds_is_enabled **
    A.pts_to uds full_perm uds0
  )
  ensures (
    uds_is_enabled **
    exists (uds1:Seq.seq U8.t). (
      A.pts_to uds full_perm uds1 **
      pure (uds1 `Seq.equal` Seq.create (US.v l) 0uy))
  )
{
  fill_array l uds 0uy;
}
```

assume
val read_uds (uds:A.larray U8.t (US.v uds_len))
             (#s:Ghost.erased (Seq.seq U8.t))
  : stt unit 
      (A.pts_to uds full_perm s `star` uds_is_enabled)
      (fun _ -> A.pts_to uds full_perm uds_bytes `star` uds_is_enabled)

```pulse
fn compute_cdi (cdi:cdi_t) (uds:A.larray U8.t (US.v uds_len)) (record:engine_record_t) 
               (#repr:Ghost.erased engine_record_repr)
               (#c0:Ghost.erased (Seq.seq U8.t))
  requires (
    uds_is_enabled **
    A.pts_to uds full_perm uds_bytes **
    A.pts_to cdi full_perm c0 **
    engine_record_perm record repr (* should CDI only be computed on authentic l0 images? *)
  )
  ensures (
    uds_is_enabled **
    engine_record_perm record repr **
    A.pts_to uds full_perm uds_bytes **
    exists (c1:Seq.seq U8.t). (
      A.pts_to cdi full_perm c1 **
      pure (cdi_functional_correctness c1 repr))
  )
{
    // let uds = new_array 0uy uds_len;
    let uds_digest = new_array 0uy dice_digest_len;
    let l0_digest = new_array 0uy dice_digest_len;
    // read_uds uds;
    hacl_hash dice_hash_alg uds uds_len uds_digest;

    unfold engine_record_perm record repr;
    hacl_hash dice_hash_alg record.l0_binary record.l0_binary_size l0_digest;
    fold engine_record_perm record repr;

    dice_digest_len_is_hashable;

    hacl_hmac dice_hash_alg cdi 
      uds_digest dice_digest_len
      l0_digest dice_digest_len;

    free_array l0_digest;
    free_array uds_digest;
    // free_array uds;
    ()
}
```

#set-options "--print_implicits --print_universes"
// ```pulse
// fn engine_main (cdi:cdi_t) (ctxt:(t:context_t{Engine_context? t})) (record:engine_record_t)
//                (#c0:Ghost.erased (Seq.seq U8.t))
//                (#repr:Ghost.erased engine_record_repr)
//   requires (
//     uds_is_enabled **
//     A.pts_to cdi full_perm c0 **
//     engine_record_perm record repr
//   )
//   returns opt: option context_t
//   ensures exists (c1:Seq.seq U8.t). (
//       A.pts_to cdi full_perm c1 **
//       engine_record_perm record repr **
//       pure (Some? opt ==> l0_is_authentic repr /\ cdi_functional_correctness c1 repr)
//   )
// {
//   let b = authenticate_l0_image record;
//   if b 
//   {
//     compute_cdi cdi ctxt.uds record;
//     Some (mk_l0_context cdi)
//   }
//   else
//   {
//     disable_uds ();
//     None #context_t
//   }
// }
// ```
```pulse
fn engine_main (cdi:cdi_t) (uds:A.larray U8.t (US.v uds_len)) (record:engine_record_t)
               (#c0:Ghost.erased (Seq.seq U8.t))
               (#repr:Ghost.erased engine_record_repr)
  requires (
    uds_is_enabled **
    A.pts_to uds full_perm uds_bytes **
    A.pts_to cdi full_perm c0 **
    engine_record_perm record repr
  )
  returns r:dice_return_code
  ensures (
    engine_record_perm record repr **
    A.pts_to uds full_perm (Seq.create (US.v uds_len) 0uy) **
    exists (c1:Seq.seq U8.t). (
      A.pts_to cdi full_perm c1 **
      pure (r = DICE_SUCCESS ==> l0_is_authentic repr /\ cdi_functional_correctness c1 repr)
  ))
{
  let b = authenticate_l0_image record;
  if b 
  {
    compute_cdi cdi uds record;
    zeroize_uds uds uds_len;
    disable_uds();
    DICE_SUCCESS
  }
  else
  {
    zeroize_uds uds uds_len;
    disable_uds ();
    DICE_ERROR
  }
}
```
