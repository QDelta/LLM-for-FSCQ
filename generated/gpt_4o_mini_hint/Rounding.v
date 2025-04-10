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
(* original proof tokens: 65 *)

(* No more tactics to try *)
Admitted.

Lemma mul_div : forall a b,
    a mod b = 0 ->
    b > 0 ->
    a / b * b = a.
(* hint proof tokens: 74 *)
Proof.
    intros.
    erewrite Nat.div_mod with (x := a) (y := b) by lia.
    rewrite H, Nat.add_0_r.
    setoid_rewrite Nat.mul_comm at 2.
    rewrite Nat.div_mul by lia.
    setoid_rewrite Nat.mul_comm at 2; auto.
  Qed.
Lemma lt_add_lt_sub : forall a b c,
    b <= a -> a < b + c -> a - b < c.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma lt_div_mul_add_le : forall a b c,
    b > 0 -> a < c / b -> b + a * b <= c.
(* hint proof tokens: 75 *)
Proof.
    intros.
    apply lt_le_S in H0.
    apply mult_le_compat_r with ( p := b ) in H0; auto.
    rewrite Nat.add_comm, <- Nat.mul_succ_l.
    eapply le_trans; eauto.
    rewrite Nat.mul_comm.
    apply Nat.mul_div_le; lia.
  Qed.
Lemma lt_div_mul_lt : forall a b c,
    b > 0 -> a < c / b -> a * b < c.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Lemma div_lt_mul_lt : forall a b c,
    b > 0 -> a / b < c -> a < c * b.
(* hint proof tokens: 68 *)
Proof.
    intros.
    apply lt_le_S in H0.
    apply mult_le_compat_r with ( p := b ) in H0; auto.
    eapply lt_le_trans; [ | eauto ].
    rewrite Nat.mul_comm.
    apply Nat.mul_succ_div_gt; lia.
  Qed.
Lemma sub_round_eq_mod : forall a b, b <> 0 -> a - a / b * b = a mod b.
(* hint proof tokens: 21 *)
Proof.
    intros.
    rewrite Nat.mod_eq, mult_comm; auto.
  Qed.
Lemma mult_neq_0 : forall m n, m <> 0 -> n <> 0 -> m * n <> 0.
(* hint proof tokens: 12 *)
Proof.
    intros. intuition.
  Qed.
Lemma mul_ge_l : forall m n,
    0 < m -> n <= n * m.
(* hint proof tokens: 30 *)
Proof.
    intros.
    rewrite mult_comm.
    destruct (mult_O_le n m); solve [ lia | auto].
  Qed.
Lemma mul_ge_r : forall m n,
    0 < m -> n <= m * n.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma div_mul_le : forall a b : addr, a / b * b <= a.
Proof.
(* original proof tokens: 48 *)

(* No more tactics to try *)
Admitted.

Lemma sub_sub_assoc : forall a b,
    a >= b -> a - (a - b) = b.
(* hint proof tokens: 12 *)
Proof.
    intros; lia.
  Qed.
Lemma sub_mod_eq_round : forall a b, b <> 0 -> a - (a mod b) = a / b * b.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_ge: forall x sz,
      sz > 0 ->
      roundup x sz >= x.
Proof.
(* original proof tokens: 185 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_ge_divisor : forall x sz, 0 < x -> roundup x sz >= sz.
Proof.
(* original proof tokens: 62 *)

(* No more tactics to try *)
Admitted.

Lemma divup_ok:
    forall x,
      divup x valubytes * valubytes >= x.
Proof.
(* original proof tokens: 24 *)
induction x; simpl; try lia.
apply Nat.le_succ_l.
(* No more tactics to try *)
Admitted.

Lemma divup_0:
    forall x,
    divup 0 x = 0.
(* hint proof tokens: 30 *)
Proof.
    intros.
    case_eq x; intros.
    reflexivity.
    apply Nat.div_small.
    lia.
  Qed.
Lemma roundup_0:
    forall x,
    roundup 0 x = 0.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma divup_1: forall x,
    divup x 1 = x.
Proof.
(* original proof tokens: 70 *)

(* No more tactics to try *)
Admitted.

Lemma divup_divup_eq:
    forall x,
      (divup ((divup x valubytes)*valubytes) valubytes) * valubytes =
      (divup x valubytes) * valubytes.
(* hint proof tokens: 94 *)
Proof.
    unfold divup; intros.
    rewrite <- Nat.add_sub_assoc by ( rewrite valubytes_is; lia ).
    rewrite Nat.div_add_l by ( rewrite valubytes_is; lia ).
    rewrite Nat.mul_add_distr_r.
    replace ((valubytes - 1) / valubytes * valubytes) with 0. lia.
    rewrite valubytes_is.
    compute.
    auto.
  Qed.
Lemma divup_lt_arg: forall x sz,
    divup x sz <= x.
(* hint proof tokens: 236 *)
Proof.
    intros.
    case_eq sz; intros.
    
    simpl. lia.
    case_eq x; intros.
    
    rewrite divup_0; constructor.
    unfold divup.
    
    rewrite Nat.div_mod with (y := S n) by lia.
    rewrite <- H.
    rewrite <- H0.
    apply le_trans with (sz * x / sz).
    apply Nat.div_le_mono.
    lia.
    replace (sz) with (1 + (sz - 1)) at 2 by lia.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_1_l.
    replace (x + sz - 1) with (x + (sz - 1)).
    apply plus_le_compat_l.
    replace x with (n0 + 1) by lia.
    rewrite Nat.mul_add_distr_l.
    rewrite plus_comm.
    rewrite Nat.mul_1_r.
    apply le_plus_l.
    lia.
    rewrite mult_comm.
    rewrite Nat.div_mul by lia.
    apply Nat.eq_le_incl.
    apply Nat.div_mod.
    lia.
  Qed.
Lemma divup_ge : forall a b c,
    b > 0 -> 
    c >= divup a b -> c * b >= a.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Lemma divup_mono: forall m n sz,
    m <= n -> divup m sz <= divup n sz.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_mono : forall m n sz,
    m <= n -> roundup m sz <= roundup n sz.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
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
(* original proof tokens: 202 *)

(* No more tactics to try *)
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
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma divup_eq_div : forall a b, a mod b = 0 -> divup a b = a / b.
(* hint proof tokens: 49 *)
Proof.
    intros.
    case_eq b; intros; auto. subst.
    rewrite divup_eq_divup'_m_nonzero by auto. unfold divup'.
    destruct (a mod S n); intuition.
  Qed.
Lemma div_le_divup : forall n sz,
    n / sz <= divup n sz.
(* hint proof tokens: 41 *)
Proof.
    intros.
    destruct sz.
    - simpl.
      lia.
    - unfold divup.
      apply Nat.div_le_mono.
      lia.
      lia.
  Qed.
Lemma div_lt_divup : forall m n sz,
    sz <> 0 ->
    m < n ->
    m / sz < divup n sz.
(* hint proof tokens: 122 *)
Proof.
    intros.
    rewrite divup_eq_divup'_m_nonzero by auto.
    unfold divup'.
    case_eq (n mod sz); intros.
    rewrite Nat.mul_lt_mono_pos_l with (p := sz) by lia.
    replace (sz * (n / sz)) with n.
    eapply le_lt_trans.
    apply Nat.mul_div_le.
    lia.
    assumption.
    apply Nat.div_exact; assumption.
    apply le_lt_trans with (n / sz).
    apply Nat.div_le_mono; lia.
    lia.
  Qed.
Lemma le_divup:
    forall m n,
      m <= n ->
      divup m valubytes <= divup n valubytes.
(* hint proof tokens: 19 *)
Proof.
    intros.
    apply divup_mono; assumption.
  Qed.
Lemma le_roundup:
    forall m n,
      m <= n ->
      roundup m valubytes <= roundup n valubytes.
(* hint proof tokens: 33 *)
Proof.
    unfold roundup, divup; intros.
    apply Nat.mul_le_mono_r.
    apply le_divup; assumption.
  Qed.
Lemma lt_minus':
    forall a b c,
      a < c -> a - b < c.
Proof.
(* original proof tokens: 13 *)

(* No more tactics to try *)
Admitted.

Lemma divup_goodSize:
    forall (a: waddr),
      goodSize addrlen (divup #a valubytes).
(* hint proof tokens: 210 *)
Proof.
    assert (addrlen > 1) by ( unfold addrlen ; lia ).
    generalize dependent addrlen.
    intros.
    unfold goodSize, divup.
    apply Nat.div_lt_upper_bound.
    rewrite valubytes_is; auto.
    apply lt_minus'.
    unfold addrlen.
    rewrite valubytes_is.
    replace (4096) with (pow2 12) by reflexivity.
    rewrite <- pow2_add_mul.
    replace (pow2 (12 + n)) with (pow2 (11 + n) + pow2 (11 + n)).
    apply plus_lt_compat.
    eapply lt_trans.
    apply natToWord_goodSize.
    apply pow2_inc; lia.
    apply pow2_inc; lia.
    replace (12 + n) with ((11 + n) + 1) by lia.
    rewrite (pow2_add_mul (11+n) 1).
    simpl (pow2 1).
    lia.
  Qed.
Lemma divup_sub_1 : forall n sz,
    n >= sz -> sz <> 0 ->
    divup (n - sz) sz = divup n sz - 1.
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Lemma divup_sub : forall i n sz,
    n >= i * sz -> sz <> 0 ->
    divup (n - i * sz) sz = divup n sz - i.
(* hint proof tokens: 70 *)
Proof.
    induction i; intros; simpl.
    repeat rewrite Nat.sub_0_r; auto.
    replace (n - (sz + i * sz)) with ((n - sz) - (i * sz)) by nia.
    rewrite IHi by nia.
    rewrite divup_sub_1; nia.
  Qed.
Lemma sub_mod_add_mod : forall a b,
    b <> 0 -> b - a mod b + a mod b = b.
(* hint proof tokens: 25 *)
Proof.
    intros.
    pose proof (Nat.mod_upper_bound a b H).
    lia.
  Qed.
Lemma divup_mul_l : forall b c,
    divup (c * b) b <= c.
(* hint proof tokens: 45 *)
Proof.
    intros; destruct (Nat.eq_dec b 0); subst.
    rewrite Nat.mul_0_r; rewrite divup_0; lia.
    rewrite divup_mul; lia.
  Qed.
Lemma divup_mul_r : forall b c,
    divup (b * c) b <= c.
(* hint proof tokens: 21 *)
Proof.
    intros; rewrite Nat.mul_comm; apply divup_mul_l.
  Qed.
Lemma divup_le : forall a b c,
    a <= b * c -> divup a b <= c.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma divup_le_1 : forall a b,
    a <= b -> divup a b <= 1.
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Lemma divup_ge_1 : forall a b,
   b <> 0 -> a >= b -> divup a b >= 1.
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma divup_small : forall c n, 0 < c <= n -> divup c n = 1.
(* hint proof tokens: 104 *)
Proof.
    intros.
    assert (divup c n <= 1) by (apply divup_le_1; lia).
    assert (c - 1 < n) by lia.
    assert ((c - 1) / n < divup c n) by (apply div_lt_divup; lia).
    assert ((c - 1) / n = 0) as HH by (apply Nat.div_small; auto); rewrite HH in *.
    lia.
  Qed.
Lemma divup_mul_ge : forall a b c,
    b <> 0 -> a >= b * c -> divup a b >= c.
(* hint proof tokens: 43 *)
Proof.
    intros.
    eapply le_trans.
    2: apply divup_mono; eauto.
    rewrite Nat.mul_comm.
    rewrite divup_mul; auto.
  Qed.
Lemma divup_gt_0 : forall a b, 0 < a -> 0 < b -> divup a b > 0.
(* hint proof tokens: 19 *)
Proof.
    intros.
    apply Nat.div_str_pos; lia.
  Qed.
Lemma mod_div_0 : forall a b,
    (a mod b) / b = 0.
Proof.
(* original proof tokens: 43 *)
intros.
rewrite Nat.mod_small; auto.
apply Nat.div_small; auto.
(* No more tactics to try *)
Admitted.

Lemma div_add_distr_le : forall a b c,
    a / c + b / c <= (a + b) / c.
(* hint proof tokens: 186 *)
Proof.
    intros.
    destruct (Nat.eq_dec c 0); subst; simpl; auto.
    rewrite Nat.div_mod with (x := a) (y := c) by auto.
    rewrite Nat.div_mod with (x := b) (y := c) by auto.
    replace (c * (a / c) + a mod c + (c * (b / c) + b mod c)) with
            (((a mod c + b mod c) + (b / c) * c) + (a / c) * c) by nia.
    repeat rewrite Nat.div_add by auto.
    setoid_rewrite Nat.add_comm at 2 3.
    setoid_rewrite Nat.mul_comm.
    repeat rewrite Nat.div_add by auto.
    repeat rewrite mod_div_0.
    repeat rewrite Nat.add_0_l.
    lia.
  Qed.
Lemma divup_add' : forall i n sz,
    sz <> 0 -> n <> 0 ->
    divup (n + sz * i) sz = divup n sz + i.
Proof.
(* original proof tokens: 134 *)

(* No more tactics to try *)
Admitted.

Lemma divup_add : forall i n sz,
    sz <> 0 -> divup (n + sz * i) sz = divup n sz + i.
Proof.
(* original proof tokens: 57 *)

(* No more tactics to try *)
Admitted.

Lemma divup_n_mul_n_le : forall a n, n <> 0 -> a <= (divup a n) * n.
(* hint proof tokens: 153 *)
Proof.
    intros.
    destruct (addr_eq_dec a 0); subst; try lia.
    eapply (Nat.div_mod a) in H as HH.
    rewrite HH.
    rewrite plus_comm.
    rewrite divup_add by lia.
    rewrite Nat.mul_add_distr_r.
    destruct (addr_eq_dec (a mod n) 0) as [H'|H'].
    rewrite H'.
    rewrite mul_div; lia.
    rewrite divup_small.
    simpl. rewrite plus_0_r.
    pose proof Nat.mod_upper_bound a n H.
    rewrite mult_comm; lia.
    split. lia.
    apply Nat.lt_le_incl. apply Nat.mod_upper_bound.
    lia.
  Qed.
Lemma add_lt_upper_bound : forall a b c d,
    a <= b -> c + b < d -> c + a < d.
(* hint proof tokens: 12 *)
Proof.
    intros; lia.
  Qed.
Lemma helper_sub_add_cancel : forall a b c,
    a >= b -> b >= c ->
    a - b + (b - c) = a - c.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma helper_add_sub_lt : forall a b c,
    b > 0 -> a < c -> a + b - c < b.
(* hint proof tokens: 12 *)
Proof.
    intros. lia.
  Qed.
Lemma div_mul_lt : forall a b,
    b <> 0 -> a mod b <> 0 -> a / b * b < a.
Proof.
(* original proof tokens: 89 *)

(* No more tactics to try *)
Admitted.

Theorem roundup_mult_mono : forall n a b, b <> 0 ->
    Nat.divide a b -> roundup n a <= roundup n b.
Proof.
(* original proof tokens: 293 *)

(* No more tactics to try *)
Admitted.

Lemma min_roundup : forall a b z, roundup (min a b) z = min (roundup a z) (roundup b z).
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_mult : forall a b, roundup (a * b) a = a * b.
(* hint proof tokens: 78 *)
Proof.
    unfold roundup; intros.
    destruct (Nat.eq_dec a 0); subst; simpl; auto.
    replace (a * b) with (b * a) by apply mult_comm.
    destruct (Nat.eq_dec b 0); subst; simpl.
    rewrite divup_0; auto.
    rewrite divup_mul; auto.
  Qed.
Lemma roundup_sub_lt : forall n sz,
    sz > 0 -> roundup n sz - n < sz.
(* hint proof tokens: 79 *)
Proof.
    unfold roundup; intros.
    divup_cases.
    replace (n / sz * sz) with n; try lia.
    rewrite Nat.mul_comm.
    rewrite Nat.div_exact; lia.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.

    apply helper_add_sub_lt; auto.
    apply div_mul_lt; lia.
  Qed.
Lemma roundup_subt_divide : forall a b c, a < roundup b c -> Nat.divide c a ->
    roundup (b - a) c = roundup b c - a.
Proof.
(* original proof tokens: 100 *)

(* No more tactics to try *)
Admitted.

Lemma divup_add_small : forall m n k,
    k > 0 -> n <= roundup m k - m ->
    divup (m + n) k = divup m k.
(* hint proof tokens: 226 *)
Proof.
    unfold roundup, divup; intros.
    replace (m + n + k - 1) with ((m + k - 1) + n) by lia.
    rewrite Nat.div_mod with (x := (m + k -1)) (y := k) by lia.
    rewrite Nat.mul_comm.
    rewrite <- Nat.add_assoc.
    repeat rewrite Nat.div_add_l by lia.
    f_equal.
    repeat rewrite Nat.div_small; auto.
    apply Nat.mod_upper_bound; lia.

    eapply add_lt_upper_bound; eauto.
    rewrite Nat.mod_eq by lia.
    rewrite Nat.mul_comm.

    destruct (le_gt_dec (m + k - 1) ((m + k - 1) / k * k)).
    replace (m + k - 1 - (m + k - 1) / k * k ) with 0 by lia.
    rewrite Nat.add_0_l.

    apply roundup_sub_lt; auto.
    rewrite helper_sub_add_cancel; try lia.
    apply roundup_ge; auto.
  Qed.
Lemma divup_divup: forall x sz,
      sz > 0 ->
      divup ((divup x sz) * sz) sz = divup x sz.
Proof.
(* original proof tokens: 58 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_roundup : forall n sz,
    sz > 0 ->
    roundup (roundup n sz) sz = roundup n sz.
(* hint proof tokens: 22 *)
Proof.
    unfold roundup; intros.
    rewrite divup_divup; auto.
  Qed.
Lemma roundup_roundup_add : forall x n sz,
    sz > 0 ->
    roundup (roundup n sz + x) sz = roundup n sz + roundup x sz.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Lemma divup_same : forall x,
    x <> 0 -> divup x x = 1.
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Lemma divup_gt : forall a b sz,
    sz > 0 -> divup a sz > b -> a > b * sz.
(* hint proof tokens: 245 *)
Proof.
    intros a b sz H.
    divup_cases.
    eapply Nat.mul_lt_mono_pos_r in H1; eauto.
    replace (a / sz * sz) with a in H1; auto.
    rewrite Nat.mul_comm.
    apply Nat.div_exact; lia.

    destruct b.
    destruct (Nat.eq_dec a 0); subst.
    contradict H0.
    rewrite Nat.mod_0_l; lia.
    lia.

    rewrite Nat.add_1_r in H1.
    apply lt_n_Sm_le in H1.
    eapply Nat.mul_le_mono_pos_r in H1; eauto.
    replace (a / sz * sz) with (a - a mod sz) in H1.
    rewrite H0 in H1.
    eapply Nat.le_lt_trans; eauto.
    destruct (Nat.eq_dec a 0); subst.
    contradict H0.
    rewrite Nat.mod_0_l; lia.
    lia.

    rewrite Nat.mod_eq by lia.
    setoid_rewrite Nat.mul_comm at 2.
    apply sub_sub_assoc.
    apply Nat.mul_div_le; lia.
  Qed.
Definition divup_S x sz :=
    match (x mod sz) with
    | O => divup x sz + 1
    | S _ => divup x sz
    end.
Theorem divup_eq_divup_S : forall x sz,
    sz <> 0 ->
    divup (S x) sz = divup_S x sz.
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Lemma divup_add_gt : forall a b n sz,
    sz > 0 -> a + divup b sz > n ->
    a * sz + b > n * sz.
(* hint proof tokens: 100 *)
Proof.
    induction a; intros; auto.
    rewrite Nat.add_0_l in H0.
    rewrite Nat.add_0_l.
    apply divup_gt; auto.

    replace (S a * sz + b) with (a * sz + (b + sz * 1)).
    apply IHa; auto.
    rewrite divup_add; lia.
    rewrite Nat.mul_1_r.
    rewrite Nat.mul_succ_l.
    lia.
  Qed.
Lemma roundup_le' : forall a b sz,
    sz > 0 ->
    a <= b * sz -> roundup a sz <= b * sz.
(* hint proof tokens: 57 *)
Proof.
    intros.
    apply (roundup_mono _ _ sz) in H0.
    eapply le_trans; eauto.
    unfold roundup.
    apply Nat.mul_le_mono_pos_r; auto.
    apply divup_mul_l.
  Qed.
Lemma roundup_le : forall a b sz,
    a <= b * sz -> roundup a sz <= b * sz.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_min_r : forall a b,
    b > 0 -> Nat.min ((divup a b) * b ) a = a.
(* hint proof tokens: 23 *)
Proof.
    intros.
    apply Nat.min_r.
    apply roundup_ge; auto.
  Qed.
Lemma divup_eq_div_plus_1 : forall a b,
    b <> 0 -> a mod b <> 0 -> divup a b = a / b + 1.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_gt : forall a b, b <> 0 -> a mod b <> 0 -> a < roundup a b.
(* hint proof tokens: 89 *)
Proof.
    intros.
    unfold roundup.
    rewrite divup_eq_div_plus_1 by auto.
    rewrite Nat.mul_add_distr_r. rewrite mult_1_l.
    rewrite Nat.div_mod with (x := a) (y := b) at 1 by auto.
    rewrite mult_comm.
    assert (a mod b < b) by (apply Nat.mod_upper_bound; auto). lia.
  Qed.
Lemma roundup_eq : forall a n, n <> 0 -> a mod n <> 0 -> roundup a n = a + (n - a mod n).
Proof.
(* original proof tokens: 131 *)

(* No more tactics to try *)
Admitted.

