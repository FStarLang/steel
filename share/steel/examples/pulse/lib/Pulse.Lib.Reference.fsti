(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.Reference
open FStar.Tactics
open PulseCore.Observability
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32

val ref ([@@@unused] a:Type u#0) : Type u#0

val pts_to
    (#a:Type) (r:ref a) 
    (#[exact (`full_perm)] [@@@equate_by_smt] p:perm)
    ([@@@equate_by_smt] n:a)
  : vprop

[@@deprecated "Reference.alloc is unsound; use Box.alloc instead"]
val alloc (#a:Type) (x:a)
  : stt (ref a) emp (fun r -> pts_to r x)
  
val ( ! ) (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  : stt a
        (pts_to r #p n)
        (fun x -> pts_to r #p n ** pure (reveal n == x))

val ( := ) (#a:Type) (r:ref a) (x:a) (#n:erased a)
  : stt unit
        (pts_to r n) 
        (fun _ -> pts_to r (hide x))

[@@deprecated "Reference.free is unsound; use Box.free instead"]
val free (#a:Type) (r:ref a) (#n:erased a)
  : stt unit (pts_to r n) (fun _ -> emp)

val share (#a:Type) (r:ref a) (#v:erased a) (#p:perm)
  : stt_ghost unit
      (pts_to r #p v)
      (fun _ ->
       pts_to r #(half_perm p) v **
       pts_to r #(half_perm p) v)

val gather (#a:Type) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  : stt_ghost unit
      (pts_to r #p0 x0 ** pts_to r #p1 x1)
      (fun _ -> pts_to r #(sum_perm p0 p1) x0 ** pure (x0 == x1))

(* Share/gather specialized to half permission *)
val share2 (#a:Type) (r:ref a) (#v:erased a)
  : stt_ghost unit
      (pts_to r v)
      (fun _ -> pts_to r #one_half v ** pts_to r #one_half v)

val gather2 (#a:Type) (r:ref a) (#x0 #x1:erased a)
  : stt_ghost unit
      (pts_to r #one_half x0 ** pts_to r #one_half x1)
      (fun _ -> pts_to r x0 ** pure (x0 == x1))

val read_atomic (r:ref U32.t) (#n:erased U32.t) (#p:perm)
  : stt_atomic U32.t #Observable emp_inames
    (pts_to r #p n)
    (fun x -> pts_to r #p n ** pure (reveal n == x))

val write_atomic (r:ref U32.t) (x:U32.t) (#n:erased U32.t)
  : stt_atomic unit #Observable emp_inames
        (pts_to r n) 
        (fun _ -> pts_to r (hide x))

val write_atomic_bool (r:ref bool) (x:bool) (#n:erased bool)
  : stt_atomic unit #Observable emp_inames
        (pts_to r n) 
        (fun _ -> pts_to r (hide x))



let cond b (p q:vprop) = if b then p else q

val cas (r:ref U32.t) (u v:U32.t) (#i:erased U32.t)
  : stt_atomic bool #Observable emp_inames 
    (pts_to r i)
    (fun b ->
      cond b (pts_to r v ** pure (reveal i == u)) 
             (pts_to r i))

val with_local
  (#a:Type0)
  (init:a)
  (#pre:vprop)
  (#ret_t:Type)
  (#post:ret_t -> vprop)
  (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
                              (fun v -> post v ** op_exists_Star (pts_to r)))
  : stt ret_t pre post


val pts_to_injective_eq (#a:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  : stt_ghost unit
      (pts_to r #p v0 ** pts_to r #q v1)
      (fun _ -> pts_to r #p v0 ** pts_to r #q v1 ** pure (v0 == v1))

val pts_to_perm_bound (#a:_) (#p:_) (r:ref a) (#v:a)
  : stt_ghost unit
      (pts_to r #p v)
      (fun _ -> pts_to r #p v ** pure (p `lesser_equal_perm` full_perm))

val replace (#a:Type0) (r:ref a) (x:a) (#v:erased a)
  : stt a
      (pts_to r v)
      (fun res -> pts_to r x ** pure (res == reveal v))
