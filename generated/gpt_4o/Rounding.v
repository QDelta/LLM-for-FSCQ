Require Import Arith Lia.
Require Import Word.
Require Import WordAuto.
Require Import Psatz.
Require Import AsyncDisk.
Import Valulen.
Definition divup (n unitsz : nat) : nat := (n + unitsz - 1) / unitsz.
Definition roundup (n unitsz:nat) : nat := (divup n unitsz) * unitsz.
Lemma div_le_mul : forall n a b,
    b > 0 -> a > 0 -> n / a <= n * b.
Proof.
(* skipped proof tokens: 65 *)
Admitted.
Lemma mul_div : forall a b,
    a mod b = 0 ->
    b > 0 ->
    a / b * b = a.
Proof.
(* skipped proof tokens: 74 *)
Admitted.
Lemma lt_add_lt_sub : forall a b c,
    b <= a -> a < b + c -> a - b < c.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma lt_div_mul_add_le : forall a b c,
    b > 0 -> a < c / b -> b + a * b <= c.
Proof.
(* skipped proof tokens: 75 *)
Admitted.
Lemma lt_div_mul_lt : forall a b c,
    b > 0 -> a < c / b -> a * b < c.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma div_lt_mul_lt : forall a b c,
    b > 0 -> a / b < c -> a < c * b.
Proof.
(* skipped proof tokens: 68 *)
Admitted.
Lemma sub_round_eq_mod : forall a b, b <> 0 -> a - a / b * b = a mod b.
Proof.
(* original proof tokens: 21 *)
(* generated proof tokens: 17 *)
intros.
rewrite Nat.mod_eq; [lia | assumption].
Qed.

Lemma mult_neq_0 : forall m n, m <> 0 -> n <> 0 -> m * n <> 0.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma mul_ge_l : forall m n,
    0 < m -> n <= n * m.
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Lemma mul_ge_r : forall m n,
    0 < m -> n <= m * n.
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Lemma div_mul_le : forall a b : addr, a / b * b <= a.
Proof.
(* skipped proof tokens: 48 *)
Admitted.
Lemma sub_sub_assoc : forall a b,
    a >= b -> a - (a - b) = b.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma sub_mod_eq_round : forall a b, b <> 0 -> a - (a mod b) = a / b * b.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Lemma roundup_ge: forall x sz,
      sz > 0 ->
      roundup x sz >= x.
Proof.
(* skipped proof tokens: 185 *)
Admitted.
Lemma roundup_ge_divisor : forall x sz, 0 < x -> roundup x sz >= sz.
Proof.
(* skipped proof tokens: 62 *)
Admitted.
Lemma divup_ok:
    forall x,
      divup x valubytes * valubytes >= x.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma divup_0:
    forall x,
    divup 0 x = 0.
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Lemma roundup_0:
    forall x,
    roundup 0 x = 0.
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Lemma divup_1: forall x,
    divup x 1 = x.
Proof.
(* skipped proof tokens: 70 *)
Admitted.
Lemma divup_divup_eq:
    forall x,
      (divup ((divup x valubytes)*valubytes) valubytes) * valubytes =
      (divup x valubytes) * valubytes.
Proof.
(* skipped proof tokens: 94 *)
Admitted.
Lemma divup_lt_arg: forall x sz,
    divup x sz <= x.
Proof.
(* skipped proof tokens: 236 *)
Admitted.
Lemma divup_ge : forall a b c,
    b > 0 -> 
    c >= divup a b -> c * b >= a.
Proof.
(* skipped proof tokens: 44 *)
Admitted.
Lemma divup_mono: forall m n sz,
    m <= n -> divup m sz <= divup n sz.
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Lemma roundup_mono : forall m n sz,
    m <= n -> roundup m sz <= roundup n sz.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Definition divup' x m :=
  match (x mod m) with
  | O => x / m
  | S _ => x / m + 1
  end.
Theorem divup_eq_divup'_m_nonzero : forall x m,
    m <> 0 ->
    divup x m = divup' x m.
Proof.
(* skipped proof tokens: 202 *)
Admitted.
Ltac divup_cases :=
    rewrite divup_eq_divup'_m_nonzero;
    [ match goal with
      [ |- context[divup' ?x ?m] ] =>
        unfold divup';
        case_eq (x mod m); intros
      end
    | try lia
    ].
Lemma divup_mul : forall x m,
    m <> 0 ->
    divup (x*m) m = x.
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Lemma divup_eq_div : forall a b, a mod b = 0 -> divup a b = a / b.
Proof.
(* skipped proof tokens: 49 *)
Admitted.
Lemma div_le_divup : forall n sz,
    n / sz <= divup n sz.
Proof.
(* skipped proof tokens: 41 *)
Admitted.
Lemma div_lt_divup : forall m n sz,
    sz <> 0 ->
    m < n ->
    m / sz < divup n sz.
Proof.
(* skipped proof tokens: 122 *)
Admitted.
Lemma le_divup:
    forall m n,
      m <= n ->
      divup m valubytes <= divup n valubytes.
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Lemma le_roundup:
    forall m n,
      m <= n ->
      roundup m valubytes <= roundup n valubytes.
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Lemma lt_minus':
    forall a b c,
      a < c -> a - b < c.
Proof.
(* skipped proof tokens: 13 *)
Admitted.
Lemma divup_goodSize:
    forall (a: waddr),
      goodSize addrlen (divup #a valubytes).
Proof.
(* skipped proof tokens: 210 *)
Admitted.
Lemma divup_sub_1 : forall n sz,
    n >= sz -> sz <> 0 ->
    divup (n - sz) sz = divup n sz - 1.
Proof.
(* original proof tokens: 66 *)
intros n sz Hnz Hsz.
divup_cases.
- rewrite divup_eq_div; try lia.
assert (n = sz + (n - sz)) by lia.
rewrite H0 in H.
rewrite H0 in H.
rewrite H0 in *.
rewrite Nat.add_sub_assoc in H by lia.
rewrite <- H0 in H.
rewrite Nat.add_sub_assoc in H by lia.
rewrite Nat.add_sub_assoc by lia.
rewrite H0 in H.
rewrite H0 in H.
(* Reached max number of model calls *)
Admitted.

Lemma divup_sub : forall i n sz,
    n >= i * sz -> sz <> 0 ->
    divup (n - i * sz) sz = divup n sz - i.
Proof.
(* skipped proof tokens: 70 *)
Admitted.
Lemma sub_mod_add_mod : forall a b,
    b <> 0 -> b - a mod b + a mod b = b.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma divup_mul_l : forall b c,
    divup (c * b) b <= c.
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma divup_mul_r : forall b c,
    divup (b * c) b <= c.
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Lemma divup_le : forall a b c,
    a <= b * c -> divup a b <= c.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma divup_le_1 : forall a b,
    a <= b -> divup a b <= 1.
Proof.
(* skipped proof tokens: 17 *)
Admitted.
Lemma divup_ge_1 : forall a b,
   b <> 0 -> a >= b -> divup a b >= 1.
Proof.
(* skipped proof tokens: 50 *)
Admitted.
Lemma divup_small : forall c n, 0 < c <= n -> divup c n = 1.
Proof.
(* original proof tokens: 104 *)

(* No more tactics to try *)
Admitted.

Lemma divup_mul_ge : forall a b c,
    b <> 0 -> a >= b * c -> divup a b >= c.
Proof.
(* skipped proof tokens: 43 *)
Admitted.
Lemma divup_gt_0 : forall a b, 0 < a -> 0 < b -> divup a b > 0.
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Lemma mod_div_0 : forall a b,
    (a mod b) / b = 0.
Proof.
(* skipped proof tokens: 43 *)
Admitted.
Lemma div_add_distr_le : forall a b c,
    a / c + b / c <= (a + b) / c.
Proof.
(* skipped proof tokens: 186 *)
Admitted.
Lemma divup_add' : forall i n sz,
    sz <> 0 -> n <> 0 ->
    divup (n + sz * i) sz = divup n sz + i.
Proof.
(* skipped proof tokens: 134 *)
Admitted.
Lemma divup_add : forall i n sz,
    sz <> 0 -> divup (n + sz * i) sz = divup n sz + i.
Proof.
(* skipped proof tokens: 57 *)
Admitted.
Lemma divup_n_mul_n_le : forall a n, n <> 0 -> a <= (divup a n) * n.
Proof.
(* skipped proof tokens: 153 *)
Admitted.
Lemma add_lt_upper_bound : forall a b c d,
    a <= b -> c + b < d -> c + a < d.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma helper_sub_add_cancel : forall a b c,
    a >= b -> b >= c ->
    a - b + (b - c) = a - c.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma helper_add_sub_lt : forall a b c,
    b > 0 -> a < c -> a + b - c < b.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma div_mul_lt : forall a b,
    b <> 0 -> a mod b <> 0 -> a / b * b < a.
Proof.
(* skipped proof tokens: 89 *)
Admitted.
Theorem roundup_mult_mono : forall n a b, b <> 0 ->
    Nat.divide a b -> roundup n a <= roundup n b.
Proof.
(* skipped proof tokens: 293 *)
Admitted.
Lemma min_roundup : forall a b z, roundup (min a b) z = min (roundup a z) (roundup b z).
Proof.
(* skipped proof tokens: 55 *)
Admitted.
Lemma roundup_mult : forall a b, roundup (a * b) a = a * b.
Proof.
(* skipped proof tokens: 78 *)
Admitted.
Lemma roundup_sub_lt : forall n sz,
    sz > 0 -> roundup n sz - n < sz.
Proof.
(* skipped proof tokens: 79 *)
Admitted.
Lemma roundup_subt_divide : forall a b c, a < roundup b c -> Nat.divide c a ->
    roundup (b - a) c = roundup b c - a.
Proof.
(* skipped proof tokens: 100 *)
Admitted.
Lemma divup_add_small : forall m n k,
    k > 0 -> n <= roundup m k - m ->
    divup (m + n) k = divup m k.
Proof.
(* skipped proof tokens: 226 *)
Admitted.
Lemma divup_divup: forall x sz,
      sz > 0 ->
      divup ((divup x sz) * sz) sz = divup x sz.
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Lemma roundup_roundup : forall n sz,
    sz > 0 ->
    roundup (roundup n sz) sz = roundup n sz.
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Lemma roundup_roundup_add : forall x n sz,
    sz > 0 ->
    roundup (roundup n sz + x) sz = roundup n sz + roundup x sz.
Proof.
(* skipped proof tokens: 42 *)
Admitted.
Lemma divup_same : forall x,
    x <> 0 -> divup x x = 1.
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Lemma divup_gt : forall a b sz,
    sz > 0 -> divup a sz > b -> a > b * sz.
Proof.
(* skipped proof tokens: 245 *)
Admitted.
Definition divup_S x sz :=
    match (x mod sz) with
    | O => divup x sz + 1
    | S _ => divup x sz
    end.
Theorem divup_eq_divup_S : forall x sz,
    sz <> 0 ->
    divup (S x) sz = divup_S x sz.
Proof.
(* skipped proof tokens: 55 *)
Admitted.
Lemma divup_add_gt : forall a b n sz,
    sz > 0 -> a + divup b sz > n ->
    a * sz + b > n * sz.
Proof.
(* skipped proof tokens: 100 *)
Admitted.
Lemma roundup_le' : forall a b sz,
    sz > 0 ->
    a <= b * sz -> roundup a sz <= b * sz.
Proof.
(* skipped proof tokens: 57 *)
Admitted.
Lemma roundup_le : forall a b sz,
    a <= b * sz -> roundup a sz <= b * sz.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Lemma roundup_min_r : forall a b,
    b > 0 -> Nat.min ((divup a b) * b ) a = a.
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Lemma divup_eq_div_plus_1 : forall a b,
    b <> 0 -> a mod b <> 0 -> divup a b = a / b + 1.
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Lemma roundup_gt : forall a b, b <> 0 -> a mod b <> 0 -> a < roundup a b.
Proof.
(* skipped proof tokens: 89 *)
Admitted.
Lemma roundup_eq : forall a n, n <> 0 -> a mod n <> 0 -> roundup a n = a + (n - a mod n).
Proof.
(* skipped proof tokens: 131 *)
Admitted.
