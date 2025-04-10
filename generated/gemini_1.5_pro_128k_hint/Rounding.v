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
(* hint proof tokens: 65 *)
Proof.
    intros.
    destruct n.
    destruct a; cbv; auto.
    destruct a; try lia.
    eapply le_trans.
    apply div_le; auto.
    rewrite Nat.mul_comm.
    destruct (mult_O_le (S n) b); auto; lia.
  Qed.
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
(* hint proof tokens: 25 *)
Proof.
    intros.
    apply lt_div_mul_add_le in H0; auto; lia.
  Qed.
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
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma mult_neq_0 : forall m n, m <> 0 -> n <> 0 -> m * n <> 0.
(* hint proof tokens: 12 *)
Proof.
    intros. intuition.
  Qed.
Lemma mul_ge_l : forall m n,
    0 < m -> n <= n * m.
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Lemma mul_ge_r : forall m n,
    0 < m -> n <= m * n.
(* hint proof tokens: 21 *)
Proof.
    intros. rewrite mult_comm. apply mul_ge_l; auto.
  Qed.
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
(* hint proof tokens: 37 *)
Proof.
    intros.
    rewrite <- sub_round_eq_mod at 1 by auto.
    rewrite sub_sub_assoc; auto.
    apply div_mul_le.
  Qed.
Lemma roundup_ge: forall x sz,
      sz > 0 ->
      roundup x sz >= x.
Proof.
(* skipped proof tokens: 185 *)
Admitted.
Lemma roundup_ge_divisor : forall x sz, 0 < x -> roundup x sz >= sz.
(* hint proof tokens: 62 *)
Proof.
    unfold roundup; intros.
    case_eq sz; intros; subst; auto.
    unfold ge.
    rewrite <- mult_1_l at 1.
    apply mult_le_compat; auto.
    unfold divup.
    apply Nat.div_str_pos; lia.
  Qed.
Lemma divup_ok:
    forall x,
      divup x valubytes * valubytes >= x.
(* hint proof tokens: 24 *)
Proof.
    intros.
    apply roundup_ge.
    rewrite valubytes_is; lia.
  Qed.
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
(* hint proof tokens: 44 *)
Proof.
    intros.
    apply le_trans with (m := divup a b * b).
    apply roundup_ge; auto.
    apply Nat.mul_le_mono_pos_r; auto.
  Qed.
Lemma divup_mono: forall m n sz,
    m <= n -> divup m sz <= divup n sz.
(* hint proof tokens: 35 *)
Proof.
    intros.
    case_eq sz; intros.
    reflexivity.
    apply Nat.div_le_mono.
    auto.
    lia.
  Qed.
Lemma roundup_mono : forall m n sz,
    m <= n -> roundup m sz <= roundup n sz.
(* hint proof tokens: 37 *)
Proof.
    intros.
    unfold roundup.
    apply Nat.mul_le_mono_nonneg_r.
    lia.
    apply divup_mono; assumption.
  Qed.
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
(* hint proof tokens: 46 *)
Proof.
    intros.
    rewrite divup_eq_divup'_m_nonzero by auto.
    unfold divup'.
    rewrite Nat.mod_mul by assumption.
    apply Nat.div_mul.
    assumption.
  Qed.
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
(* hint proof tokens: 13 *)
Proof.
    intros.
    lia.
  Qed.
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
intros. divup_cases.
(* No more tactics to try *)
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
(* hint proof tokens: 45 *)
Proof.
    intros; destruct (Nat.eq_dec b 0); subst.
    rewrite Nat.mul_0_r; rewrite divup_0; lia.
    rewrite divup_mul; lia.
  Qed.
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
(* hint proof tokens: 50 *)
Proof.
    intros; unfold divup.
    replace (a + b - 1) with (a - 1 + 1 * b) by lia.
    rewrite Nat.div_add by auto.
    nia.
  Qed.
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
(* hint proof tokens: 19 *)
Proof.
    intros.
    apply Nat.div_str_pos; lia.
  Qed.
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
(* hint proof tokens: 134 *)
Proof.
    induction i; intros; simpl.
    rewrite Nat.add_0_r; rewrite Nat.mul_0_r; auto.
    replace (n + (sz * S i)) with ((n + sz) + (sz * i)) by nia.
    rewrite IHi by nia.
    unfold divup.
    replace (n + sz + sz - 1) with (n - 1 + 2 * sz) by nia.
    replace (n + sz - 1) with (n - 1 + 1 * sz) by nia.
    repeat rewrite Nat.div_add by auto.
    lia.
  Qed.
Lemma divup_add : forall i n sz,
    sz <> 0 -> divup (n + sz * i) sz = divup n sz + i.
Proof.
(* skipped proof tokens: 57 *)
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
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma helper_sub_add_cancel : forall a b c,
    a >= b -> b >= c ->
    a - b + (b - c) = a - c.
(* hint proof tokens: 12 *)
Proof.
    intros; lia.
  Qed.
Lemma helper_add_sub_lt : forall a b c,
    b > 0 -> a < c -> a + b - c < b.
(* hint proof tokens: 12 *)
Proof.
    intros. lia.
  Qed.
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
(* hint proof tokens: 55 *)
Proof.
    intros.
    edestruct Min.min_spec as [ [HH Hmin]|[HH Hmin] ]; rewrite Hmin in *;
    symmetry; (apply min_l || apply min_r);
    apply roundup_mono; lia.
  Qed.
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
(* hint proof tokens: 58 *)
Proof.
    unfold divup; intros.
    rewrite <- Nat.add_sub_assoc by lia.
    rewrite Nat.div_add_l by lia.
    replace ((sz - 1) / sz) with 0. lia.
    rewrite Nat.div_small; lia.
  Qed.
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
(* hint proof tokens: 42 *)
Proof.
    unfold roundup; intros.
    rewrite Nat.add_comm.
    setoid_rewrite Nat.mul_comm at 2.
    rewrite divup_add by lia.
    lia.
  Qed.
Lemma divup_same : forall x,
    x <> 0 -> divup x x = 1.
Proof.
(* skipped proof tokens: 30 *)
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
(* skipped proof tokens: 55 *)
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
Proof.
(* skipped proof tokens: 57 *)
Admitted.
Lemma roundup_le : forall a b sz,
    a <= b * sz -> roundup a sz <= b * sz.
(* hint proof tokens: 37 *)
Proof.
    destruct sz; intros.
    unfold roundup.
    repeat rewrite Nat.mul_0_r; auto.
    apply roundup_le'; auto; lia.
  Qed.
Lemma roundup_min_r : forall a b,
    b > 0 -> Nat.min ((divup a b) * b ) a = a.
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Lemma divup_eq_div_plus_1 : forall a b,
    b <> 0 -> a mod b <> 0 -> divup a b = a / b + 1.
(* hint proof tokens: 21 *)
Proof.
    intros.
    divup_cases.
    contradiction.
    auto.
  Qed.
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
(* hint proof tokens: 131 *)
Proof.
    intros.
    unfold roundup.
    rewrite divup_eq_divup'_m_nonzero by auto. unfold divup'.
    destruct (a mod n) as [|n'] eqn:HH; intuition.
    replace (S n') with (a mod n) by lia.
    rewrite Nat.div_mod with (x := a) (y := n) at 2 by auto.
    rewrite <- plus_assoc.
    rewrite <- le_plus_minus by (apply Nat.lt_le_incl, Nat.mod_upper_bound; auto).
    rewrite Nat.mul_add_distr_r. rewrite mult_comm. lia.
  Qed.
