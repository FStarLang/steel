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

module Pulse.Soundness.Lift
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

let elab_lift_stt_atomic_st_typing (g:stt_env)
  (c1 c2:ln_comp)
  (e:R.term)
  (e_typing:RT.tot_typing (elab_env g) e (elab_comp c1))
  (lc:lift_comp g c1 c2) = admit ()

let elab_lift_stt_ghost_unobservable_typing (g:stt_env)
  (c1 c2:ln_comp)
  (e:R.term)
  (e_typing:RT.tot_typing (elab_env g) e (elab_comp c1))
  (lc:lift_comp g c1 c2)
  (reveal_a:R.term)
  (reveal_a_typing:RT.tot_typing (elab_env g) reveal_a
                                 (non_informative_witness_rt (comp_u c1)
                                                             (elab_term (comp_res c1)))) = admit ()

let elab_lift_stt_unobservable_atomic_typing (g:stt_env)
  (c1 c2:ln_comp)
  (e:R.term)
  (e_typing:RT.tot_typing (elab_env g) e (elab_comp c1))
  (lc:lift_comp g c1 c2) = admit ()
