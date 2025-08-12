module Steel.ST.GenArraySwap.Proof

open FStar.Math.Lemmas
open FStar.Mul
module SZ = FStar.SizeT

#set-options "--z3cliopt smt.arith.nl=false"

let lemma_mod_lt
  (a:int)
  (b:pos)
: Lemma
  (let r = a % b in 0 <= r /\ r < b)
  [SMTPat (a % b)]
= ()

let lemma_mul_nat_nat_is_nat
  (a b: nat)
: Lemma
  (a * b >= 0)
  [SMTPat (a * b)]
= ()

let lemma_pos_mul_pos_args
  (a: nat)
  (b: nat)
: Lemma
  (requires (a * b > 0))
  (ensures (a > 0 /\ b > 0 /\ a <= a * b /\ b <= a * b /\ a * b == b * a))
= ()

let lemma_div_nat
  (a: nat)
  (b: pos)
: Lemma
  (a / b >= 0)
  [SMTPat (a / b)]
= ()

let lemma_mult_reg_l
  (k: int)
  (x1 x2: int)
: Lemma
  (requires (
    k * x1 == k * x2 /\
    k <> 0
  ))
  (ensures (
    x1 == x2
  ))
= ()

let lemma_bezout_one_zero
  (x1: int)
  (x2: nat)
  (y1 y2: int)
: Lemma
  (requires (
    x1 * x2 + y1 * y2 == 1 /\
    y1 == 0
  ))
  (ensures (
    x1 == 1 /\ x2 == 1
  ))
= ()

let int_semiring () =
  FStar.Tactics.CanonCommSemiring.int_semiring ();
  FStar.Tactics.trefl ();
  FStar.Tactics.qed ()

[@@erasable]
noeq
type bezout_t = {
  d: pos;
  q_n: nat;
  q_l: nat;
  u_n: int;
  u_l: int;
}

let bezout_prop'
  (n: nat)
  (l: nat)
  (d: pos)
  (q_n: nat)
  (q_l: nat)
  (u_n: int)
  (u_l: int)
: Tot prop
= n == d * q_n /\
  l == d * q_l /\
  d == n * u_n + l * u_l

let bezout_prop
  (n: nat)
  (l: nat)
  (b: bezout_t)
: Tot prop
= bezout_prop' n l b.d b.q_n b.q_l b.u_n b.u_l

let bezout
  (n: nat)
  (l: nat)
: Tot Type
= (b: bezout_t { bezout_prop n l b })

#restart-solver
let rec mk_bezout
  (n: pos)
  (l: nat)
: Pure (bezout n l)
  (requires (l < n))
  (ensures (fun _ -> True))
  (decreases l)
= if l = 0
  then begin
    let d : pos = n in
    let q_n : nat = 1 in
    let q_l : nat = 0 in
    let u_n : int = 1 in
    let u_l : int = 0 in
    let res = {
      d = d;
      q_n = q_n;
      q_l = q_l;
      u_n = u_n;
      u_l = u_l;
    }
    in
    assert (eq2 #int n (d * q_n)) by (int_semiring ());
    assert (eq2 #int 0 (d * q_l)) by (int_semiring ());
    assert (eq2 #int d (n * 1 + 0 * res.u_l)) by (int_semiring ());
    res
  end
  else begin
    let lpre = n % l in
    let ql = n / l in
    euclidean_division_definition n l;
    let bpre = mk_bezout l lpre in
    let d = bpre.d in
    let q_l = bpre.q_n in
    let qpre_lpre = bpre.q_l in
    let upre_l = bpre.u_n in
    let upre_lpre = bpre.u_l in
    let n_alt0 = l * ql + lpre in
    assert (n == n_alt0);
    let l_alt = d * q_l in
    let lpre_alt1 = d * qpre_lpre in
    let n_alt1 = l_alt * ql + lpre_alt1 in
    assert (n_alt1 == n);
    let q_n = q_l * ql + qpre_lpre in
    assert (eq2 #int n_alt1 (d * q_n)) by (int_semiring ());
    let lpre_alt2 = n + - l * ql in
    assert (lpre_alt2 == lpre);
    let d_alt = l * upre_l + lpre_alt2 * upre_lpre in
    assert (d_alt == d);
    let u_l = upre_l + - ql * upre_lpre in
    assert (eq2 #int (n * upre_lpre + l * u_l) d_alt) by (int_semiring ());
    let res = {
      d = d;
      q_n = q_n;
      q_l = q_l;
      u_n = upre_lpre;
      u_l = u_l;
    }
    in
    res
  end

let bezout_q_eq
  (n: nat)
  (l: nat)
  (bz: bezout n l)
: Lemma
  (bz.q_n == n / bz.d)
  [SMTPat (bezout_prop n l bz); SMTPat bz.q_n]
= cancel_mul_div bz.q_n bz.d

let rec iter_fun
  (#t: Type)
  (f: (t -> GTot t))
  (n: nat)
  (x: t)
: GTot t
  (decreases n)
= if n = 0
  then x
  else iter_fun f (n - 1) (f x)

let nat_up_to (n: nat) : Tot Type = (i: nat { i < n })

let jump
  (n: pos)
  (l: nat)
  (x: nat_up_to n)
: GTot (nat_up_to n)
= (x + l) % n

#restart-solver
let jump_mod_d
  (n: pos)
  (l: nat)
  (b: bezout n l)
  (x: nat_up_to n)
: Lemma
  (jump n l x % b.d == x % b.d)
=
  let x' = jump n l x in
  let x'q = (x + l) / n in
  euclidean_division_definition (x + l) n;
  let l_alt = b.d * b.q_l in
  assert (l_alt == l);
  let n_alt = b.d * b.q_n in
  assert (n_alt == n);
  let x'_alt = x + l_alt + - x'q * n_alt in
  assert (x'_alt == x');
  let qx = b.q_l + - x'q * b.q_n in
  assert (eq2 #int x'_alt (x + qx * b.d)) by (int_semiring ());
  lemma_mod_plus x qx b.d

let rec jump_iter_mod_d
  (n: pos)
  (l: nat)
  (b: bezout n l)
  (x: nat_up_to n)
  (k: nat)
: Lemma
  (ensures (iter_fun #(nat_up_to n) (jump n l) k x % b.d == x % b.d))
  (decreases k)
= if k = 0
  then ()
  else begin
    jump_mod_d n l b x;
    jump_iter_mod_d n l b (jump n l x) (k - 1)
  end

(* Coverage *)

let rec jump_iter
  (n: pos)
  (l: nat)
  (x: nat_up_to n)
  (k: nat)
: Lemma
  (ensures (iter_fun #(nat_up_to n) (jump n l) k x == (x + k * l) % n))
  (decreases k)
= if k = 0
  then begin
    assert (eq2 #int (x + 0 * l) x) by (int_semiring ());
    small_mod x n
  end else begin
    let k' = k - 1 in
    assert (eq2 #int (x + (k' + 1) * l) ((x + l) + k' * l)) by (int_semiring ());
    jump_iter n l ((x + l) % n) k';
    lemma_mod_add_distr (k' * l) (x + l) n
  end

let bezout_pos_le
  (n: pos)
  (l: nat)
  (b: bezout n l)
: Lemma
  (b.d <= n /\ b.q_n > 0)
  [SMTPat (bezout_prop n l b)]
= lemma_pos_mul_pos_args b.q_n b.d

#restart-solver
[@@"opaque_to_smt"]
irreducible
let jump_coverage
  (n: pos)
  (l: nat)
  (b: bezout n l)
  (x: nat_up_to n)
: Ghost nat
  (requires True)
  (ensures (fun k ->
    x == iter_fun (jump n l) k (x % b.d)
  ))
=
  let i = x % b.d in
  let qx = x / b.d in
  euclidean_division_definition x b.d;
  let k1 = qx * b.u_l in
  let m = qx * b.u_n in
  assert (eq2 #int (qx * (n * b.u_n + l * b.u_l) + i) (i + k1 * l + m * n)) by (int_semiring ());
  assert (x == i + k1 * l + m * n);
  small_mod x n;
  lemma_mod_plus (i + k1 * l) m n;
  assert (x == (i + k1 * l) % n);
  let k = k1 % n in
  let qk = k1 / n in
  euclidean_division_definition k1 n;
  assert (i + (qk * n + k) * l == i + k * l + (qk * l) * n) by (int_semiring ());
  lemma_mod_plus (i + k * l) (qk * l) n;
  assert (eq2 #int x ((i + k * l) % n));
  jump_iter n l i k;
  k

[@@"opaque_to_smt"]
irreducible
let rec minimal_exists'
  (p: (nat -> GTot bool))
  (n: nat)
  (i: nat)
: Ghost nat
  (requires (
    p n == true /\
    i <= n /\
    (forall (j: nat) . j < i ==> p j == false)
  ))
  (ensures (fun k ->
    p k == true /\
    (forall (j: nat) . j < k ==> p j == false)
  ))
  (decreases (n - i))
= if p i
  then i
  else minimal_exists' p n (i + 1)

[@@"opaque_to_smt"]
irreducible
let minimal_exists
  (p: (nat -> GTot bool))
  (n: nat)
: Ghost nat
  (requires (
    p n == true
  ))
  (ensures (fun k ->
    p k == true /\
    (forall (j: nat) . j < k ==> p j == false)
  ))
= minimal_exists' p n 0

[@@"opaque_to_smt"]
irreducible
let jump_coverage_strong
  (n: pos)
  (l: nat)
  (b: bezout n l)
  (x: nat_up_to n)
: Ghost nat
  (requires True)
  (ensures (fun k ->
    x == iter_fun (jump n l) k (x % b.d) /\
    (forall (k': nat) . k' < k ==> (~ (x == iter_fun (jump n l) k' (x % b.d))))
  ))
= let k' = jump_coverage n l b x in
  minimal_exists (fun k -> x = iter_fun (jump n l) k (x % b.d)) k'

#restart-solver
let jump_iter_mod_q
  (n: pos)
  (l: nat)
  (b: bezout n l)
  (x: nat_up_to n)
  (k: nat)
: Lemma
  (ensures (
    b.q_n > 0 /\
    iter_fun (jump n l) (k % b.q_n) x == iter_fun (jump n l) k x
  ))
= assert (b.q_n > 0);
  let k' = k % b.q_n in
  let qk = k / b.q_n in
  euclidean_division_definition k b.q_n;
  jump_iter n l x k';
  jump_iter n l x k;
  assert (eq2 #int (x + (qk * b.q_n + k') * (b.d * b.q_l)) (x + k' * (b.d * b.q_l) + (qk * b.q_l) * (b.d * b.q_n))) by (int_semiring ());
  assert (x + k * l == x + k' * l + (qk * b.q_l) * n);
  lemma_mod_plus (x + k' * l) (qk * b.q_l) n

let jump_coverage_strong_bound
  (n: pos)
  (l: nat)
  (b: bezout n l)
  (x: nat_up_to n)
: Lemma
  (b.q_n > 0 /\
    jump_coverage_strong n l b x < b.q_n
  )
  [SMTPat (jump_coverage_strong n l b x)]
= let k = jump_coverage_strong n l b x in
  jump_iter_mod_q n l b (x % b.d) k

#restart-solver

[@@"opaque_to_smt"]
irreducible
let mod_eq_elim
  (n: pos)
  (x1 x2: int)
: Ghost int
  (requires (x1 % n == x2 % n))
  (ensures (fun k -> x1 - x2 == k * n))
= euclidean_division_definition x1 n;
  euclidean_division_definition x2 n;
  let q1 = x1 / n in
  let q2 = x2 / n in
  let k = q1 + - q2 in
  let r = x1 % n in
  assert (q1 * n + r + - (q2 * n + r) == k * n) by (int_semiring ());
  k

let mod_eq_intro
  (n: pos)
  (x1 x2: int)
  (k: int)
: Lemma
  (requires (x1 - x2 == k * n))
  (ensures (x1 % n == x2 % n))
= lemma_mod_plus x2 k n

#restart-solver
[@@"opaque_to_smt"]
irreducible
let gauss
  (n: pos)
  (l: pos) // necessary here
  (b: bezout n l)
  (kl kn: int)
: Ghost int
  (requires (
    kl * l == kn * n
  ))
  (ensures (fun k ->
    kl == k * b.q_n
  ))
= assert ((b.d * b.q_n) * b.u_n + (b.d * b.q_l) * b.u_l == b.d * (b.u_n * b.q_n + b.u_l * b.q_l)) by (int_semiring ());
  assert (b.d == b.d * 1) by (int_semiring ());
  assert (b.d * (b.u_n * b.q_n + b.u_l * b.q_l) == b.d * 1);
  lemma_mult_reg_l b.d (b.u_n * b.q_n + b.u_l * b.q_l) 1;
  assert (b.u_n * b.q_n + b.u_l * b.q_l == 1);
  if b.u_l = 0
  then begin
    lemma_bezout_one_zero b.u_n b.q_n b.u_l b.q_l;
    assert (b.q_n == 1);
    assert (kl * 1 == kl) by (int_semiring ());
    kl
  end else begin
    assert (kl * (b.d * b.q_l) == kn * (b.d * b.q_n));
    assert (kl * (b.d * b.q_l) == b.d * (kl * b.q_l)) by (int_semiring ());
    assert (kn * (b.d * b.q_n) == b.d * (kn * b.q_n)) by (int_semiring ());
    assert (b.d * (kl * b.q_l) == b.d * (kn * b.q_n));
    lemma_mult_reg_l b.d (kl * b.q_l) (kn * b.q_n);
    assert (kl * b.q_l == kn * b.q_n);
    assert (b.u_l * (kl * b.q_l) == b.u_l * (kn * b.q_n));
    assert (b.u_l * (kl * b.q_l) == kl * (b.u_l * b.q_l)) by (int_semiring ());
    assert (b.u_l * (kn * b.q_n) == (kn * b.u_l) * b.q_n) by (int_semiring ());
    assert (kl * (b.u_l * b.q_l) == (kn * b.u_l) * b.q_n);
    assert (kl * (1 + - (b.u_n * b.q_n)) == kl + - kl * b.u_n * b.q_n) by (int_semiring ());
    assert (kl * b.u_n * b.q_n + (kn * b.u_l) * b.q_n == (kn * b.u_l + kl * b.u_n) * b.q_n) by (int_semiring ());
    kn * b.u_l + kl * b.u_n
  end

let jump_iter_mod_q_inj_weak
  (n: pos)
  (l: pos)
  (b: bezout n l)
  (x: nat_up_to n)
  (k1 k2: nat)
: Lemma
  (requires (
    iter_fun (jump n l) k1 x == iter_fun (jump n l) k2 x
  ))
  (ensures (
    b.q_n > 0 /\
    k1 % b.q_n == k2 % b.q_n
  ))
= jump_iter n l x k1;
  jump_iter n l x k2;
  let kn = mod_eq_elim n (x + k1 * l) (x + k2 * l) in
  assert ((k1 + - k2) * l == (k1 * l + - (k2 * l))) by (int_semiring ());
  let kq = gauss n l b (k1 + - k2) kn in
  mod_eq_intro b.q_n k1 k2 kq

let jump_iter_inj
  (n: nat)
  (l: nat)
  (b: bezout_t)
  (i1 i2: nat)
  (k1 k2: nat)
: Lemma
  (requires (
    n > 0 /\
    l > 0 /\
    bezout_prop n l b /\
    i1 < b.d /\
    i2 < b.d /\
    k1 < b.q_n /\
    k2 < b.q_n /\
    iter_fun (jump n l) k1 i1 == iter_fun (jump n l) k2 i2
  ))
  (ensures (
    i1 == i2 /\
    k1 == k2
  ))
  [SMTPat (iter_fun (jump n l) k1 i1); SMTPat (iter_fun (jump n l) k2 i2); SMTPat (bezout_prop n l b)]
= jump_iter_mod_d n l b i1 k1;
  jump_iter_mod_d n l b i2 k2;
  small_mod i1 b.d;
  small_mod i2 b.d;
  jump_iter_mod_q_inj_weak n l b i1 k1 k2;
  small_mod k1 b.q_n;
  small_mod k2 b.q_n
  
#restart-solver
let jump_iter_elim
  (n: pos)
  (p: nat_up_to n -> prop)
  (l: nat)
  (b: bezout n l)
: Lemma
  (requires (
    forall (i: nat_up_to b.d) (k: nat_up_to b.q_n) . p (iter_fun (jump n l) k i)
  ))
  (ensures (
    forall (x: nat_up_to n) . p x
  ))
= let prf
    (x: nat_up_to n)
  : Lemma
    (p x)
  =
    let i : nat_up_to b.d = x % b.d in
    let k' = jump_coverage_strong n l b x in
    jump_coverage_strong_bound n l b x;
    assert (p (iter_fun (jump n l) k' i))
  in
  Classical.forall_intro prf

let jump_if
  (n: pos)
  (l: nat)
  (sq: squash (l < n))
  (idx: nat_up_to n)
: Lemma
  (jump n l idx == (if idx + l >= n then idx - (n - l) else idx + l))
= let idx' = (if idx + l >= n then idx - (n - l) else idx + l) in
  small_mod idx n;
  small_mod idx' n;
  lemma_mod_plus (idx + l) (-1) n

let jump_iter_q
  (n: pos)
  (l: nat)
  (b: bezout n l)
  (x: nat_up_to n)
: Lemma
  (ensures (
    iter_fun (jump n l) b.q_n x == x
  ))
= cancel_mul_mod 1 b.q_n;
  jump_iter_mod_q n l b x b.q_n

let rec iter_fun_add
  (#t: Type)
  (f: (t -> GTot t))
  (n1 n2: nat)
  (x: t)
: Lemma
  (ensures (iter_fun f n1 (iter_fun f n2 x) == iter_fun f (n1 + n2) x))
  (decreases n2)
= if n2 = 0
  then ()
  else iter_fun_add f n1 (n2 - 1) (f x)

let iter_succ_l
  (#t: Type)
  (f: (t -> GTot t))
  (n: nat)
  (x: t)
: Lemma
  (f (iter_fun f n x) == iter_fun f (n + 1) x)
  [SMTPat (f (iter_fun f n x))]
= iter_fun_add f 1 n x

let jump_jump_iter_pred_q
  (n: pos)
  (l: nat)
  (b: bezout n l)
  (x: nat_up_to n)
  (j: nat_up_to b.q_n)
: Lemma
  (requires (
    j == b.q_n - 1
  ))
  (ensures (
    jump n l (iter_fun (jump n l) j x) == x
  ))
  [SMTPat (jump n l (iter_fun (jump n l) j x)); SMTPat (bezout_prop n l b)]
= jump_iter_q n l b x

let array_swap_post
  (#t: Type)
  (s0: Seq.seq t)
  (n: nat)
  (l: nat)
  (s: Seq.seq t)
: Tot prop
=
    n == Seq.length s0 /\
    0 <= l /\
    l <= n /\
    s `Seq.equal` (Seq.slice s0 l n `Seq.append` Seq.slice s0 0 l)

let array_as_ring_buffer_swap
  (#t: Type)
  (n: nat)
  (l: nat)
  (bz: bezout n l)
  (s0: Seq.seq t)
  (s: Seq.seq t)
: Lemma
  (requires (
    n == Seq.length s0 /\
    n == Seq.length s /\
    0 < l /\
    l < n /\
    (forall (i': nat_up_to bz.d) .
      (forall (j: nat_up_to bz.q_n) .
        (i' < bz.d) ==> (
        let idx = iter_fun #(nat_up_to n) (jump n l) j i' in
        Seq.index s idx == Seq.index s0 (jump n l idx)
    )))
  ))
  (ensures (
    array_swap_post s0 n l s
  ))
  [SMTPat (array_swap_post s0 n l s); SMTPat (bezout_prop n l bz)]
= Classical.forall_intro (jump_if n l ());
  let p
    (idx: nat_up_to n)
  : Tot prop
  = Seq.index s idx == Seq.index s0 (jump n l idx)
  in
  jump_iter_elim n p l bz

let array_swap_outer_invariant // hoisting necessary because "Let binding is effectful"
  (#t: Type0) (s0: Seq.seq t) (n: nat) (l: nat) (bz: bezout (n) (l))
  (s: Seq.seq t) (i: nat)
: Tot prop
= 0 < l /\
  l < n /\
  i <= bz.d /\
  n == Seq.length s0 /\
  n == Seq.length s /\
  (forall (i': nat_up_to bz.d) . // this is always true, but I need it here for the pattern
    Seq.index s i' == Seq.index s (iter_fun #(nat_up_to (n)) (jump (n) (l)) 0 i')
  ) /\ 
  (forall (i': nat_up_to bz.d) .
     (forall (j: nat_up_to bz.q_n) .
        let idx = iter_fun #(nat_up_to (n)) (jump (n) (l)) j i' in
        Seq.index s idx == Seq.index s0 (if i' < i then jump (n) (l) idx else idx)
  ))

let array_swap_inner_invariant
  (#t: Type0) (s0: Seq.seq t) (n: nat) (l: nat) (bz: bezout (n) (l))
  (s: Seq.seq t) (i: nat) (j: nat) (idx: nat)
: Tot prop
= 0 < l /\
  l < n /\
  n == Seq.length s0 /\
  i < bz.d /\
  j < bz.q_n /\
  idx == iter_fun #(nat_up_to (n)) (jump (n) (l)) (j) (i) /\
  n == Seq.length s /\
  (forall (i': nat_up_to bz.d) .
     (forall (j': nat_up_to bz.q_n) .
        let idx = iter_fun #(nat_up_to (n)) (jump (n) (l)) j' i' in
        Seq.index s idx == Seq.index s0 (if i' < i || (i' = i && j' < j) then jump (n) (l) idx else idx)
  ))

#push-options "--z3rlimit 20"
let array_swap_inner_invariant_end
  (#t: Type)
  (n: nat)
  (l: nat)
  (bz: bezout (n) (l))
  (s0: Seq.seq t)
  (s: Seq.seq t)
  (i: nat)
  (j: nat)
  (idx: nat)
: Lemma
  (requires (
    array_swap_inner_invariant s0 n l bz s i j idx /\
    (~ (j < bz.q_n - 1))
  ))
  (ensures (
    let s' = Seq.upd s idx (Seq.index s0 i) in
    array_swap_outer_invariant s0 n l bz s' (i + 1)
  ))
//  [SMTPat (array_swap_inner_invariant s0 n l bz s i j idx)]
= ()
#pop-options

let sz_rem_spec
  (n: SZ.t)
  (l: SZ.t)
: Lemma
  (requires (SZ.v l > 0))
  (ensures (SZ.v (SZ.rem n l) == SZ.v n % SZ.v l))
  [SMTPat (SZ.rem n l)]
= euclidean_division_definition (SZ.v n) (SZ.v l)
