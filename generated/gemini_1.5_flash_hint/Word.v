Require Import Arith Div2 NArith Bool Lia.
Require Import Nomega.
Require Import Wf_nat.
Require Import Eqdep_dec.
Require Import Program.Tactics.
Require Import Recdef.
Require Import Ring.
Require Import Ring_polynom.
Require Import ProofIrrelevance.
Require Import Psatz.
Set Implicit Arguments.
Inductive word : nat -> Set :=
| WO : word O
| WS : bool -> forall n, word n -> word (S n).
Fixpoint wordToNat sz (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false w' => (wordToNat w') * 2
    | WS true w' => S (wordToNat w' * 2)
  end.
Arguments wordToNat : simpl nomatch.
Definition wordToNat' sz (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false w' => 2 * wordToNat w'
    | WS true w' => S (2 * wordToNat w')
  end.
Theorem wordToNat_wordToNat' : forall sz (w : word sz),
  wordToNat w = wordToNat' w.
Proof.
(* original proof tokens: 25 *)
induction w; simpl; auto.
rewrite IHw.
(* No more tactics to try *)
Admitted.

Fixpoint mod2 (n : nat) : bool :=
  match n with
    | 0 => false
    | 1 => true
    | S (S n') => mod2 n'
  end.
Fixpoint natToWord (sz n : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS (mod2 n) (natToWord sz' (div2 n))
  end.
Definition liftWord (sz : nat) (f : nat -> nat) (w: word sz) :=
  natToWord sz (f (wordToNat w)).
Fixpoint wordToN sz (w : word sz) : N :=
  match w with
    | WO => 0
    | WS false w' => 2 * wordToN w'
    | WS true w' => N.succ (2 * wordToN w')
  end%N.
Arguments wordToN : simpl nomatch.
Definition Nmod2 (n : N) : bool :=
  match n with
    | N0 => false
    | Npos (xO _) => false
    | _ => true
  end.
Definition wzero sz := natToWord sz 0.
Fixpoint wzero' (sz : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS false (wzero' sz')
  end.
Fixpoint posToWord (sz : nat) (p : positive) {struct p} : word sz :=
  match sz with
    | O => WO
    | S sz' =>
      match p with
        | xI p' => WS true (posToWord sz' p')
        | xO p' => WS false (posToWord sz' p')
        | xH => WS true (wzero' sz')
      end
  end.
Definition NToWord (sz : nat) (n : N) : word sz :=
  match n with
    | N0 => wzero' sz
    | Npos p => posToWord sz p
  end.
Fixpoint Npow2 (n : nat) : N :=
  match n with
    | O => 1
    | S n' => 2 * Npow2 n'
  end%N.
Ltac rethink :=
  match goal with
    | [ H : ?f ?n = _ |- ?f ?m = _ ] => replace m with n; simpl; auto
  end.
Theorem mod2_S_double : forall n, mod2 (S (2 * n)) = true.
Proof.
(* original proof tokens: 15 *)
induction n; simpl.
(* No more tactics to try *)
Admitted.

Theorem mod2_double : forall n, mod2 (2 * n) = false.
Proof.
(* original proof tokens: 22 *)
induction n; simpl; auto.
(* No more tactics to try *)
Admitted.

Local Hint Resolve mod2_S_double mod2_double.
Theorem div2_double : forall n, div2 (2 * n) = n.
Proof.
(* original proof tokens: 25 *)
(* generated proof tokens: 11 *)

apply div2_double.
Qed.

Theorem div2_S_double : forall n, div2 (S (2 * n)) = n.
Proof.
(* original proof tokens: 18 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite div2_double div2_S_double : div2.
Theorem natToWord_wordToNat : forall sz w, natToWord sz (wordToNat w) = w.
(* hint proof tokens: 56 *)
Proof.
  induction w; rewrite wordToNat_wordToNat'; intuition; f_equal; unfold natToWord, wordToNat'; fold natToWord; fold wordToNat';
    destruct b; f_equal; autorewrite with div2; intuition.
Qed.
Fixpoint pow2 (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => 2 * pow2 n'
  end.
Lemma pow2_add_mul: forall a b,
  pow2 (a + b) = (pow2 a) * (pow2 b).
(* hint proof tokens: 78 *)
Proof.
  induction a; destruct b; try now firstorder; simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_1_r; auto.
  simpl.
  repeat rewrite Nat.add_0_r.
  rewrite IHa.
  simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_add_distr_r; auto.
Qed.
Lemma mult_pow2_bound: forall a b x y,
  x < pow2 a -> y < pow2 b -> x * y < pow2 (a + b).
(* hint proof tokens: 27 *)
Proof.
  intros.
  rewrite pow2_add_mul.
  apply Nat.mul_lt_mono_nonneg; lia.
Qed.
Lemma mult_pow2_bound_ex: forall a c x y,
  x < pow2 a -> y < pow2 (c - a) -> c >= a -> x * y < pow2 c.
(* hint proof tokens: 32 *)
Proof.
  intros.
  replace c with (a + (c - a)) by lia.
  apply mult_pow2_bound; auto.
Qed.
Lemma lt_mul_mono' : forall c a b,
  a < b -> a < b * (S c).
(* hint proof tokens: 42 *)
Proof.
  induction c; intros.
  rewrite Nat.mul_1_r; auto.
  rewrite Nat.mul_succ_r.
  apply lt_plus_trans.
  apply IHc; auto.
Qed.
Lemma lt_mul_mono : forall a b c,
  c <> 0 -> a < b -> a < b * c.
(* hint proof tokens: 32 *)
Proof.
  intros.
  replace c with (S (c - 1)) by lia.
  apply lt_mul_mono'; auto.
Qed.
Lemma zero_lt_pow2 : forall sz, 0 < pow2 sz.
(* hint proof tokens: 13 *)
Proof.
  induction sz; simpl; lia.
Qed.
Lemma one_lt_pow2:
  forall n,
    1 < pow2 (S n).
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma mul2_add : forall n, n * 2 = n + n.
(* hint proof tokens: 14 *)
Proof.
  induction n; firstorder. lia.
Qed.
Lemma pow2_le_S : forall sz, (pow2 sz) + 1 <= pow2 (sz + 1).
Proof.
(* original proof tokens: 49 *)
(* generated proof tokens: 14 *)

induction sz; simpl; lia.
Qed.

Lemma pow2_bound_mono: forall a b x,
  x < pow2 a -> a <= b -> x < pow2 b.
(* hint proof tokens: 55 *)
Proof.
  intros.
  replace b with (a + (b - a)) by lia.
  rewrite pow2_add_mul.
  apply lt_mul_mono; auto.
  pose proof (zero_lt_pow2 (b - a)).
  lia.
Qed.
Lemma pow2_inc : forall n m,
  0 < n -> n < m ->
    pow2 n < pow2 m.
(* hint proof tokens: 100 *)
Proof.
  intros.
  generalize dependent n; intros.
  induction m; simpl.
  intros. inversion H0.
  unfold lt in H0.
  rewrite Nat.add_0_r.
  inversion H0.
  apply Nat.lt_add_pos_r.
  apply zero_lt_pow2.
  apply Nat.lt_trans with (pow2 m).
  apply IHm.
  exact H2.
  apply Nat.lt_add_pos_r.
  apply zero_lt_pow2.
Qed.
Theorem roundTrip_0 : forall sz, wordToNat (natToWord sz 0) = 0.
Proof.
(* original proof tokens: 13 *)
(* generated proof tokens: 18 *)
induction sz; simpl; auto.
rewrite IHsz; auto.
Qed.

Hint Rewrite roundTrip_0 : wordToNat.
Local Hint Extern 1 (@eq nat _ _) => lia.
Theorem untimes2 : forall n, n + (n + 0) = 2 * n.
Proof.
(* original proof tokens: 8 *)
(* generated proof tokens: 16 *)

induction n; simpl; auto; lia.
Qed.

Section strong.
Variable P : nat -> Prop.
Hypothesis PH : forall n, (forall m, m < n -> P m) -> P n.
Lemma strong' : forall n m, m <= n -> P m.
(* hint proof tokens: 27 *)
Proof.
    induction n; simpl; intuition; apply PH; intuition.
    elimtype False; lia.
  Qed.
Theorem strong : forall n, P n.
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

End strong.
Theorem div2_odd : forall n,
  mod2 n = true
  -> n = S (2 * div2 n).
Proof.
(* original proof tokens: 76 *)
intros; induction n; simpl; try lia.
inversion H.
destruct n; simpl in *; try lia.
rewrite IHn; auto.
destruct n; simpl in *; try lia.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
(* Reached max number of model calls *)
Admitted.

Theorem div2_even : forall n,
  mod2 n = false
  -> n = 2 * div2 n.
Proof.
(* original proof tokens: 73 *)

(* No more tactics to try *)
Admitted.

Lemma wordToNat_natToWord' : forall sz w, exists k, wordToNat (natToWord sz w) + k * pow2 sz = w.
(* hint proof tokens: 233 *)
Proof.
  induction sz; simpl; intuition; repeat rewrite untimes2.

  exists w; intuition.

  case_eq (mod2 w); intro Hmw.

  specialize (IHsz (div2 w)); firstorder.
  simpl wordToNat.
  rewrite wordToNat_wordToNat' in *.
  exists x; intuition.
  rewrite mult_assoc.
  rewrite (mult_comm x 2).
  rewrite mult_comm. simpl mult at 1.
  rewrite (plus_Sn_m (2 * wordToNat' (natToWord sz (div2 w)))).
  rewrite <- mult_assoc.
  rewrite <- mult_plus_distr_l.
  rewrite H; clear H.
  symmetry; apply div2_odd; auto.

  specialize (IHsz (div2 w)); firstorder.
  simpl wordToNat.
  exists x; intuition.
  rewrite mult_assoc.
  rewrite (mult_comm x 2).
  rewrite <- mult_assoc.
  rewrite mult_comm.
  rewrite <- mult_plus_distr_l.
  rewrite H; clear H.
  symmetry; apply div2_even; auto.
Qed.
Theorem wordToNat_natToWord : forall sz w, exists k, wordToNat (natToWord sz w) = w - k * pow2 sz /\ k * pow2 sz <= w.
(* hint proof tokens: 29 *)
Proof.
  intros; destruct (wordToNat_natToWord' sz w) as [k]; exists k; intuition.
Qed.
Definition wone sz := natToWord sz 1.
Fixpoint wones (sz : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS true (wones sz')
  end.
Fixpoint wmsb sz (w : word sz) (a : bool) : bool :=
  match w with
    | WO => a
    | WS b  x => wmsb x b
  end.
Definition whd sz (w : word (S sz)) : bool :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S _ => bool
                             end with
    | WO => tt
    | WS b _ => b
  end.
Definition wtl sz (w : word (S sz)) : word sz :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S sz'' => word sz''
                             end with
    | WO => tt
    | WS _ w' => w'
  end.
Theorem WS_neq : forall b1 b2 sz (w1 w2 : word sz),
  (b1 <> b2 \/ w1 <> w2)
  -> WS b1 w1 <> WS b2 w2.
Proof.
(* original proof tokens: 42 *)
intros; destruct H; auto.
congruence.
(* No more tactics to try *)
Admitted.

Fixpoint rep_bit (n : nat) (b : word 1) : word n :=
  match n as n0 return (word n0) with
  | 0 => WO
  | S n0 => WS (whd b) (rep_bit n0 b)
  end.
Lemma shatter_word : forall n (a : word n),
  match n return word n -> Prop with
    | O => fun a => a = WO
    | S _ => fun a => a = WS (whd a) (wtl a)
  end a.
(* hint proof tokens: 12 *)
Proof.
  destruct a; eauto.
Qed.
Lemma shatter_word_S : forall n (a : word (S n)),
  exists b, exists c, a = WS b c.
(* hint proof tokens: 19 *)
Proof.
  intros; repeat eexists; apply (shatter_word a).
Qed.
Lemma shatter_word_0 : forall a : word 0,
  a = WO.
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Hint Resolve shatter_word_0.
Theorem word0: forall (w : word 0), w = WO.
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 13 *)

apply shatter_word_0.
Qed.

Definition weq : forall sz (x y : word sz), {x = y} + {x <> y}.
refine (fix weq sz (x : word sz) : forall y : word sz, {x = y} + {x <> y} :=
    match x in word sz return forall y : word sz, {x = y} + {x <> y} with
      | WO => fun _ => left _ _
      | WS b x' => fun y => if bool_dec b (whd y)
        then if weq _ x' (wtl y) then left _ _ else right _ _
        else right _ _
    end); clear weq.
abstract (symmetry; apply shatter_word_0).
abstract (subst; symmetry; apply (shatter_word y)).
abstract (rewrite (shatter_word y); simpl; intro; injection H; intros;
    apply n0; apply inj_pair2_eq_dec in H0; [ auto | apply eq_nat_dec ]).
abstract (rewrite (shatter_word y); simpl; intro; apply n0; injection H; auto).
Defined.
Fixpoint weqb sz (x : word sz) : word sz -> bool :=
  match x in word sz return word sz -> bool with
    | WO => fun _ => true
    | WS b x' => fun y => 
      if eqb b (whd y)
      then if @weqb _ x' (wtl y) then true else false
      else false
  end.
Theorem weqb_true_iff : forall sz x y,
  @weqb sz x y = true <-> x = y.
Proof.
(* original proof tokens: 176 *)
induction sz; intros; simpl.
split; intros.
inversion H; subst; auto.
inversion H.
inversion H.
inversion H; subst; auto.
(* No more tactics to try *)
Admitted.

Theorem eq_rect_nat_double : forall T (a b c : nat) x ab bc,
  eq_rect b T (eq_rect a T x b ab) c bc = eq_rect a T x c (eq_trans ab bc).
(* hint proof tokens: 44 *)
Proof.
  intros.
  destruct ab.
  destruct bc.
  rewrite (UIP_dec eq_nat_dec (eq_trans eq_refl eq_refl) eq_refl).
  simpl.
  auto.
Qed.
Hint Rewrite eq_rect_nat_double.
Hint Rewrite <- (eq_rect_eq_dec eq_nat_dec).
Ltac generalize_proof :=
    match goal with
    | [ |- context[eq_rect _ _ _ _ ?H ] ] => generalize H
    end.
Ltac eq_rect_simpl :=
  unfold eq_rec_r, eq_rec;
  repeat rewrite eq_rect_nat_double;
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
Lemma eq_rect_word_offset_helper : forall a b c,
  a = b -> c + a = c + b.
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 8 *)

auto.
Qed.

Theorem eq_rect_word_offset : forall n n' offset w Heq,
  eq_rect n (fun n => word (offset + n)) w n' Heq =
  eq_rect (offset + n) (fun n => word n) w (offset + n') (eq_rect_word_offset_helper _ Heq).
(* hint proof tokens: 40 *)
Proof.
  intros.
  destruct Heq.
  rewrite (UIP_dec eq_nat_dec (eq_rect_word_offset_helper offset eq_refl) eq_refl).
  reflexivity.
Qed.
Lemma eq_rect_word_mult_helper : forall a b c,
  a = b -> a * c = b * c.
(* hint proof tokens: 12 *)
Proof.
  intros; congruence.
Qed.
Theorem eq_rect_word_mult : forall n n' scale w Heq,
  eq_rect n (fun n => word (n * scale)) w n' Heq =
  eq_rect (n * scale) (fun n => word n) w (n' * scale) (eq_rect_word_mult_helper _ Heq).
(* hint proof tokens: 40 *)
Proof.
  intros.
  destruct Heq.
  rewrite (UIP_dec eq_nat_dec (eq_rect_word_mult_helper scale eq_refl) eq_refl).
  reflexivity.
Qed.
Theorem eq_rect_word_match : forall n n' (w : word n) (H : n = n'),
  match H in (_ = N) return (word N) with
  | eq_refl => w
  end = eq_rect n (fun n => word n) w n' H.
(* hint proof tokens: 28 *)
Proof.
  intros.
  destruct H.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Theorem whd_match : forall n n' (w : word (S n)) (Heq : S n = S n'),
  whd w = whd (match Heq in (_ = N) return (word N) with
               | eq_refl => w
               end).
Proof.
(* original proof tokens: 71 *)
intros.
rewrite eq_rect_word_match in *; auto.
(* No more tactics to try *)
Admitted.

Theorem wtl_match : forall n n' (w : word (S n)) (Heq : S n = S n') (Heq' : n = n'),
  (match Heq' in (_ = N) return (word N) with
   | eq_refl => wtl w
   end) = wtl (match Heq in (_ = N) return (word N) with
               | eq_refl => w
               end).
Proof.
(* original proof tokens: 102 *)

(* No more tactics to try *)
Admitted.

Fixpoint combine (sz1 : nat) (w : word sz1) : forall sz2, word sz2 -> word (sz1 + sz2) :=
  match w in word sz1 return forall sz2, word sz2 -> word (sz1 + sz2) with
    | WO => fun _ w' => w'
    | WS b w' => fun _ w'' => WS b (combine w' w'')
  end.
Fixpoint split1 (sz1 sz2 : nat) : word (sz1 + sz2) -> word sz1 :=
  match sz1 with
    | O => fun _ => WO
    | S sz1' => fun w => WS (whd w) (split1 sz1' sz2 (wtl w))
  end.
Fixpoint split2 (sz1 sz2 : nat) : word (sz1 + sz2) -> word sz2 :=
  match sz1 with
    | O => fun w => w
    | S sz1' => fun w => split2 sz1' sz2 (wtl w)
  end.
Ltac shatterer := simpl; intuition;
  match goal with
    | [ w : _ |- _ ] => rewrite (shatter_word w); simpl
  end; f_equal; auto.
Theorem combine_split : forall sz1 sz2 (w : word (sz1 + sz2)),
  combine (split1 sz1 sz2 w) (split2 sz1 sz2 w) = w.
Proof.
(* original proof tokens: 14 *)
(* generated proof tokens: 25 *)

induction sz1; simpl; intros; try rewrite IHszt; shatterer.
Qed.

Theorem split1_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split1 sz1 sz2 (combine w z) = w.
(* hint proof tokens: 14 *)
Proof.
  induction sz1; shatterer.
Qed.
Theorem split2_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split2 sz1 sz2 (combine w z) = z.
Proof.
(* original proof tokens: 14 *)
(* generated proof tokens: 15 *)

induction sz1; shatterer.
Qed.

Hint Rewrite combine_split.
Hint Rewrite split1_combine.
Hint Rewrite split2_combine.
Theorem combine_assoc : forall n1 (w1 : word n1) n2 n3 (w2 : word n2) (w3 : word n3) Heq,
  combine (combine w1 w2) w3
  = match Heq in _ = N return word N with
      | refl_equal => combine w1 (combine w2 w3)
    end.
Proof.
(* original proof tokens: 145 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem split1_iter : forall n1 n2 n3 Heq w,
  split1 n1 n2 (split1 (n1 + n2) n3 w)
  = split1 n1 (n2 + n3) (match Heq in _ = N return word N with
                           | refl_equal => w
                         end).
Proof.
(* original proof tokens: 76 *)
intros.
rewrite eq_rect_word_match.
(* No more tactics to try *)
Admitted.

Theorem split2_iter : forall n1 n2 n3 Heq w,
  split2 n2 n3 (split2 n1 (n2 + n3) w)
  = split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                           | refl_equal => w
                         end).
(* hint proof tokens: 58 *)
Proof.
  induction n1; simpl; intuition.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)); reflexivity.

  rewrite (IHn1 _ _ (plus_assoc _ _ _)).
  f_equal.
  apply wtl_match.
Qed.
Theorem split1_split2 : forall n1 n2 n3 Heq w,
  split1 n2 n3 (split2 n1 (n2 + n3) w) =
  split2 n1 n2 (split1 (n1 + n2) n3 (match Heq in _ = N return word N with
                                     | refl_equal => w
                                     end)).
Proof.
(* original proof tokens: 101 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem split2_split1 : forall n1 n2 n3 Heq w,
  split2 n1 n2 (split1 (n1+n2) n3 w) =
  split1 n2 n3 (split2 n1 (n2+n3) (match Heq in _ = N return word N with
                                     | refl_equal => w
                                     end)).
(* hint proof tokens: 100 *)
Proof.
  induction n1; simpl; intros.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)).
  reflexivity.

  rewrite (shatter_word w).
  simpl.
  assert (n1 + n2 + n3 = n1 + (n2 + n3)) as Heq' by lia.
  rewrite <- wtl_match with (Heq':=Heq').
  rewrite <- IHn1.
  f_equal.
Qed.
Theorem combine_0_n : forall sz2 (w: word 0) (v: word sz2),
  combine w v = v.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma WS_eq_rect : forall b n (w: word n) n' H H',
  eq_rect _ word (@WS b n w) _ H = @WS b n' (eq_rect _ word w _ H').
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Theorem combine_eq_rect2 : forall sz n n'
  (H: n = n') H'
  (a: word sz) (b: word n),
  combine a b =
    eq_rect _ word (combine a (eq_rect _ word b _ H)) _ H'.
Proof.
(* original proof tokens: 45 *)
intros.
rewrite <- combine_split.
(* No more tactics to try *)
Admitted.

Theorem combine_n_0 : forall sz1 (w : word sz1) (v : word 0),
  combine w v = eq_rect _ word w _ (plus_n_O sz1).
(* hint proof tokens: 39 *)
Proof.
  induction w; intros.
  - replace v with WO; auto.
  - simpl; rewrite IHw.
    erewrite WS_eq_rect.
    reflexivity.
Qed.
Lemma whd_eq_rect : forall n w Heq,
  whd (eq_rect (S n) word w (S (n + 0)) Heq) =
  whd w.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Lemma wtl_eq_rect : forall n w Heq Heq',
  wtl (eq_rect (S n) word w (S (n + 0)) Heq) =
  eq_rect n word (wtl w) (n + 0) Heq'.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma whd_eq_rect_mul : forall n w Heq,
  whd (eq_rect (S n) word w (S (n * 1)) Heq) =
  whd w.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma wtl_eq_rect_mul : forall n w b Heq Heq',
  wtl (eq_rect (S n) word (WS b w) (S (n * 1)) Heq) =
  eq_rect _ word w _ Heq'.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Theorem split1_0 : forall n w Heq,
  split1 n 0 (eq_rect _ word w _ Heq) = w.
Proof.
(* original proof tokens: 58 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem split2_0 : forall n w Heq,
  split2 0 n (eq_rect _ word w _ Heq) = w.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Theorem combine_end : forall n1 n2 n3 Heq w,
  combine (split1 n2 n3 (split2 n1 (n2 + n3) w))
  (split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                          | refl_equal => w
                        end))
  = split2 n1 (n2 + n3) w.
Proof.
(* original proof tokens: 166 *)

(* No more tactics to try *)
Admitted.

Theorem eq_rect_combine : forall n1 n2 n2' (w1 : word n1) (w2 : word n2') Heq,
  eq_rect (n1 + n2') (fun n => word n)
    (combine w1 w2) (n1 + n2) Heq =
  combine w1 (eq_rect n2' (fun n => word n) w2 n2 (plus_reg_l _ _ _ Heq)).
Proof.
(* original proof tokens: 64 *)

(* No more tactics to try *)
Admitted.

Lemma eq_rect_combine_assoc' : forall a b c H wa wb wc,
  eq_rect (a + (b + c)) word (combine wa (combine wb wc)) _ H = combine (combine wa wb) wc.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma eq_rect_split2_helper : forall a b c,
  a = b -> c + a = c + b.
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 10 *)

congruence.
Qed.

Theorem eq_rect_split2 : forall n1 n2 n2' (w : word (n1 + n2')) Heq,
  eq_rect n2' (fun n => word n)
    (split2 n1 n2' w) n2 Heq =
  split2 n1 n2 (eq_rect (n1+n2') (fun n => word n) w (n1+n2) (eq_rect_split2_helper _ Heq)).
(* hint proof tokens: 82 *)
Proof.
  intros.
  generalize (eq_rect_split2_helper n1 Heq); intros.
  generalize dependent Heq.
  generalize dependent w.
  assert (n2' = n2) as H' by lia.
  generalize dependent e.
  rewrite H'; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Theorem eq_rect_split2_eq2 : forall n1 n2 n2' (w : word (n1 + n2)) Heq Heq2,
  eq_rect n2 (fun n => word n)
    (split2 n1 n2 w) n2' Heq =
  split2 n1 n2' (eq_rect (n1+n2) (fun n => word n) w (n1+n2') Heq2).
Proof.
(* original proof tokens: 61 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem eq_rect_split2_eq1 : forall n1 n1' n2 (w: word (n1 + n2)) Heq,
     split2 n1 n2 w = split2 n1' n2
        (eq_rect (n1 + n2) (fun y : nat => word y) w
     (n1' + n2) Heq).
Proof.
(* original proof tokens: 58 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem combine_split_eq_rect2 : forall n1 n2 n2' (w : word (n1 + n2)) Heq,
  combine (split1 n1 n2 w)
          (eq_rect n2 (fun n => word n) (split2 n1 n2 w)
                   n2' Heq) =
  eq_rect (n1 + n2) (fun n => word n) w
          (n1 + n2') (eq_rect_split2_helper _ Heq).
(* hint proof tokens: 58 *)
Proof.
  intros.
  assert (n2 = n2') by lia.
  generalize dependent Heq.
  generalize dependent w.
  rewrite <- H; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  apply combine_split.
Qed.
Lemma eq_rect_split1_helper : forall a b c,
  a = b -> a + c = b + c.
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 10 *)

congruence.
Qed.

Lemma eq_rect_split1_eq2_helper : forall a b c,
  a = b -> c + a = c + b.
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 10 *)

congruence.
Qed.

Theorem eq_rect_split1 : forall n1 n1' n2 (w : word (n1' + n2)) Heq,
  eq_rect n1' (fun n => word n)
    (split1 n1' n2 w) n1 Heq =
  split1 n1 n2 (eq_rect (n1'+n2) (fun n => word n) w (n1+n2) (eq_rect_split1_helper _ Heq)).
Proof.
(* original proof tokens: 82 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem eq_rect_split1_eq1 : forall n1 n1' n2 (w : word (n1 + n2)) Heq Heq1,
  eq_rect n1 (fun n => word n)
    (split1 n1 n2 w) n1' Heq =
  split1 n1' n2 (eq_rect (n1+n2) (fun n => word n) w (n1'+n2) Heq1).
(* hint proof tokens: 46 *)
Proof.
  intros.
  generalize dependent w.
  generalize dependent Heq1.
  rewrite Heq; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Lemma split1_eq_rect_eq1_helper : forall a b c, b = a -> a + c = b + c.
(* hint proof tokens: 13 *)
Proof. intros. subst. reflexivity. Qed.
Theorem split1_eq_rect_eq1 : forall a a' b H w,
  split1 a b w = eq_rect _ word (split1 a' b
    (eq_rect _ word w _ (split1_eq_rect_eq1_helper b H))) _ H.
(* hint proof tokens: 26 *)
Proof.
  intros a a' b H.
  subst a'; intros; eq_rect_simpl; auto.
Qed.
Theorem eq_rect_split1_eq2 : forall n1 n2 n2' (w: word (n1 + n2)) Heq,
     split1 n1 n2 w = split1 n1 n2'
        (eq_rect (n1 + n2) (fun y : nat => word y) w
     (n1 + n2') Heq).
(* hint proof tokens: 58 *)
Proof.
  intros.
  assert (n2 = n2') as H' by lia.
  generalize dependent w.
  generalize dependent Heq.
  rewrite H'; intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Fact eq_rect_combine_dist_helper1 : forall a b c d, b * c = d -> (a + b) * c = a * c + d.
(* hint proof tokens: 18 *)
Proof. intros; subst. apply Nat.mul_add_distr_r. Qed.
Fact eq_rect_combine_dist_helper2 : forall a b c d, b * c = d -> a * c + d = (a + b) * c.
(* hint proof tokens: 20 *)
Proof. intros; subst. symmetry; apply Nat.mul_add_distr_r. Qed.
Theorem eq_rect_combine_dist : forall a b c d (w : word ((a + b) * c)) (H : b * c = d),
  b * c = d ->
  let H1 := (eq_rect_combine_dist_helper1 a b c H) in
  let H2 := (eq_rect_combine_dist_helper2 a b c H) in
  let w' := eq_rec ((a + b) * c) word w _ H1 in
  w = eq_rec _ word (combine (split1 (a * c) d w') (split2 (a * c) d w')) _ H2.
Proof.
(* original proof tokens: 52 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma wzero_dist : forall a b c H,
  wzero ((a + b) * c) = eq_rect _ word (wzero (a * c + b * c)) _ H.
(* hint proof tokens: 20 *)
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.
Lemma wzero_rev : forall (a b : nat) H,
   wzero (a + b) = eq_rect _ word (wzero (b + a)) _ H.
(* hint proof tokens: 16 *)
Proof. intros a b H. rewrite H. auto. Qed.
Lemma split1_zero : forall sz1 sz2, split1 sz1 sz2 (natToWord _ O) = natToWord _ O.
(* hint proof tokens: 23 *)
Proof.
  induction sz1; auto; simpl; intros.
  f_equal. eauto.
Qed.
Lemma split2_zero : forall sz1 sz2, split2 sz1 sz2 (natToWord _ O) = natToWord _ O.
(* hint proof tokens: 12 *)
Proof.
  induction sz1; auto.
Qed.
Theorem combine_inj : forall sz1 sz2 a b c d,
  @combine sz1 a sz2 b = @combine sz1 c sz2 d -> a = c /\ b = d.
Proof.
(* original proof tokens: 115 *)
intros sz1 sz2 a b c d H.
inversion H; subst; split; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H.
inversion H.
inversion H.
induction sz1; simpl in *; intros; auto.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
(* Reached max number of model calls *)
Admitted.

Theorem combine_wzero : forall sz1 sz2, combine (wzero sz1) (wzero sz2) = wzero (sz1 + sz2).
Proof.
(* original proof tokens: 29 *)
(* generated proof tokens: 24 *)
induction sz1; simpl; auto; intros.
rewrite IHsz1.
reflexivity.
Qed.

Theorem combine_wones : forall sz1 sz2, combine (wones sz1) (wones sz2) = wones (sz1 + sz2).
Proof.
(* original proof tokens: 22 *)
(* generated proof tokens: 23 *)
induction sz1; simpl; intros; auto.
f_equal.
apply IHsz1.
Qed.

Definition sext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  if wmsb w false then
    combine w (wones sz')
  else 
    combine w (wzero sz').
Definition zext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  combine w (wzero sz').
Definition wneg sz (x : word sz) : word sz :=
  NToWord sz (Npow2 sz - wordToN x).
Definition wordBin (f : N -> N -> N) sz (x y : word sz) : word sz :=
  NToWord sz (f (wordToN x) (wordToN y)).
Definition wplus := wordBin Nplus.
Definition wmult := wordBin Nmult.
Definition wdiv := wordBin N.div.
Definition wmod := wordBin Nmod.
Definition wmult' sz (x y : word sz) : word sz := 
  split2 sz sz (NToWord (sz + sz) (Nmult (wordToN x) (wordToN y))).
Definition wminus sz (x y : word sz) : word sz := wplus x (wneg y).
Definition wnegN sz (x : word sz) : word sz :=
  natToWord sz (pow2 sz - wordToNat x).
Definition wordBinN (f : nat -> nat -> nat) sz (x y : word sz) : word sz :=
  natToWord sz (f (wordToNat x) (wordToNat y)).
Definition wplusN := wordBinN plus.
Definition wmultN := wordBinN mult.
Definition wmultN' sz (x y : word sz) : word sz := 
  split2 sz sz (natToWord (sz + sz) (mult (wordToNat x) (wordToNat y))).
Definition wminusN sz (x y : word sz) : word sz := wplusN x (wnegN y).
Delimit Scope word_scope with word.
Bind Scope word_scope with word.
Notation "w ~ 1" := (WS true w)
 (at level 7, left associativity, format "w '~' '1'") : word_scope.
Notation "w ~ 0" := (WS false w)
 (at level 7, left associativity, format "w '~' '0'") : word_scope.
Notation "^~" := wneg.
Notation "l ^+ r" := (@wplus _ l%word r%word) (at level 50, left associativity).
Notation "l ^* r" := (@wmult _ l%word r%word) (at level 40, left associativity).
Notation "l ^- r" := (@wminus _ l%word r%word) (at level 50, left associativity).
Notation "l ^/ r" := (@wdiv _ l%word r%word) (at level 50, left associativity).
Notation "l ^% r" := (@wmod _ l%word r%word) (at level 50, left associativity).
Theorem wordToN_nat : forall sz (w : word sz), wordToN w = N_of_nat (wordToNat w).
(* hint proof tokens: 85 *)
Proof.
  induction w; intuition.
  destruct b; unfold wordToN, wordToNat; fold wordToN; fold wordToNat.

  rewrite N_of_S.
  rewrite N_of_mult.
  rewrite <- IHw. 
  rewrite Nmult_comm.
  reflexivity.

  rewrite N_of_mult.
  rewrite <- IHw.
  rewrite Nmult_comm.
  reflexivity.
Qed.
Theorem mod2_S : forall n k,
  2 * k = S n
  -> mod2 n = true.
Proof.
(* original proof tokens: 57 *)
intros n k H.
(* No more tactics to try *)
Admitted.

Theorem wzero'_def : forall sz, wzero' sz = wzero sz.
Proof.
(* original proof tokens: 22 *)
(* generated proof tokens: 20 *)
induction sz; simpl; auto.
rewrite IHsz.
reflexivity.
Qed.

Theorem posToWord_nat : forall p sz, posToWord sz p = natToWord sz (nat_of_P p).
(* hint proof tokens: 246 *)
Proof.
  induction p; destruct sz; simpl; intuition; f_equal; try rewrite wzero'_def in *.
  
  rewrite Pnat.ZL6.
  destruct (Pnat.ZL4 p) as [? Heq]; rewrite Heq; simpl.
  replace (x + S x) with (S (2 * x)) by lia.
  symmetry; apply mod2_S_double.

  rewrite IHp.
  rewrite Pnat.ZL6.
  destruct (nat_of_P p); simpl; intuition.
  replace (n + S n) with (S (2 * n)) by lia.
  rewrite div2_S_double; auto.

  unfold nat_of_P; simpl.
  rewrite Pnat.ZL6.
  replace (nat_of_P p + nat_of_P p) with (2 * nat_of_P p) by lia.
  symmetry; apply mod2_double.

  rewrite IHp.
  unfold nat_of_P; simpl.
  rewrite Pnat.ZL6.
  replace (nat_of_P p + nat_of_P p) with (2 * nat_of_P p) by lia.
  rewrite div2_double.
  auto.
  auto.
Qed.
Theorem NToWord_nat : forall sz n, NToWord sz n = natToWord sz (nat_of_N n).
(* hint proof tokens: 32 *)
Proof.
  destruct n; simpl; intuition; try rewrite wzero'_def in *.
  auto.
  apply posToWord_nat.
Qed.
Theorem wplus_alt : forall sz (x y : word sz), wplus x y = wplusN x y.
(* hint proof tokens: 58 *)
Proof.
  unfold wplusN, wplus, wordBinN, wordBin; intros.

  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nplus.
  repeat rewrite nat_of_N_of_nat.
  reflexivity.
Qed.
Theorem wmult_alt : forall sz (x y : word sz), wmult x y = wmultN x y.
(* hint proof tokens: 58 *)
Proof.
  unfold wmultN, wmult, wordBinN, wordBin; intros.

  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nmult.
  repeat rewrite nat_of_N_of_nat.
  reflexivity.
Qed.
Theorem Npow2_nat : forall n, nat_of_N (Npow2 n) = pow2 n.
(* hint proof tokens: 34 *)
Proof.
  induction n; simpl; intuition.
  rewrite <- IHn; clear IHn.
  case_eq (Npow2 n); intuition.
Qed.
Theorem pow2_N : forall n, Npow2 n = N.of_nat (pow2 n).
(* hint proof tokens: 27 *)
Proof.
  intro n. apply nat_of_N_eq. rewrite Nat2N.id. apply Npow2_nat.
Qed.
Theorem wneg_alt : forall sz (x : word sz), wneg x = wnegN x.
(* hint proof tokens: 60 *)
Proof.
  unfold wnegN, wneg; intros.
  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nminus.
  do 2 f_equal.
  apply Npow2_nat.
  apply nat_of_N_of_nat.
Qed.
Theorem wminus_Alt : forall sz (x y : word sz), wminus x y = wminusN x y.
Proof.
(* original proof tokens: 26 *)
(* generated proof tokens: 29 *)
unfold wminus, wminusN; intros.
rewrite wplus_alt.
rewrite wneg_alt.
reflexivity.
Qed.

Theorem wplus_unit : forall sz (x : word sz), natToWord sz 0 ^+ x = x.
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Theorem wplus_comm : forall sz (x y : word sz), x ^+ y = y ^+ x.
Proof.
(* original proof tokens: 28 *)
unfold wplus; intros.
(* No more tactics to try *)
Admitted.

Theorem drop_mod2 : forall n k,
  2 * k <= n
  -> mod2 (n - 2 * k) = mod2 n.
(* hint proof tokens: 82 *)
Proof.
  induction n using strong; intros.

  do 2 (destruct n; simpl in *; repeat rewrite untimes2 in *; intuition).

  destruct k; simpl in *; intuition.

  destruct k; simpl; intuition.
  rewrite <- plus_n_Sm.
  repeat rewrite untimes2 in *.
  simpl; auto.
  apply H; lia.
Qed.
Theorem div2_minus_2 : forall n k,
  2 * k <= n
  -> div2 (n - 2 * k) = div2 n - k.
(* hint proof tokens: 70 *)
Proof.
  induction n using strong; intros.

  do 2 (destruct n; simpl in *; intuition; repeat rewrite untimes2 in *).
  destruct k; simpl in *; intuition.

  destruct k; simpl in *; intuition.
  rewrite <- plus_n_Sm.
  apply H; lia.
Qed.
Theorem div2_bound : forall k n,
  2 * k <= n
  -> k <= div2 n.
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Theorem drop_sub : forall sz n k,
  k * pow2 sz <= n
  -> natToWord sz (n - k * pow2 sz) = natToWord sz n.
Proof.
(* original proof tokens: 165 *)
induction sz; simpl; intros; auto.
rewrite untimes2 in H.
(* No more tactics to try *)
Admitted.

Lemma mod2_S_S : forall n,
  mod2 (S (S n)) = mod2 n.
Proof.
(* original proof tokens: 19 *)
(* generated proof tokens: 10 *)

reflexivity.
Qed.

Lemma mod2_S_not : forall n,
  mod2 (S n) = if (mod2 n) then false else true.
(* hint proof tokens: 38 *)
Proof.
  intros.
  induction n; auto.
  rewrite mod2_S_S.
  destruct (mod2 n); replace (mod2 (S n)); auto.
Qed.
Lemma mod2_S_eq : forall n k,
  mod2 n = mod2 k ->
  mod2 (S n) = mod2 (S k).
Proof.
(* original proof tokens: 25 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem drop_mod2_add : forall n k,
  mod2 (n + 2 * k) = mod2 n.
Proof.
(* original proof tokens: 79 *)
induction n; simpl; auto; intros.
(* No more tactics to try *)
Admitted.

Theorem div2_plus_2 : forall n k,
  div2 (n + 2 * k) = div2 n + k.
Proof.
(* original proof tokens: 169 *)
induction n; intros.
simpl.
(* No more tactics to try *)
Admitted.

Theorem drop_add : forall sz n k,
  natToWord sz (n + k * pow2 sz) = natToWord sz n.
(* hint proof tokens: 94 *)
Proof.
  induction sz; simpl; intuition; repeat rewrite untimes2 in *; f_equal.
  - rewrite mult_assoc.
    rewrite (mult_comm k).
    rewrite <- mult_assoc.
    apply drop_mod2_add.

  - rewrite <- (IHsz (div2 n) k).
    rewrite mult_assoc.
    rewrite (mult_comm k).
    rewrite <- mult_assoc.
    rewrite div2_plus_2.
    reflexivity.
Qed.
Local Hint Extern 1 (_ <= _) => lia.
Theorem wplus_assoc : forall sz (x y z : word sz), x ^+ (y ^+ z) = x ^+ y ^+ z.
(* hint proof tokens: 204 *)
Proof.
  intros; repeat rewrite wplus_alt; unfold wplusN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  replace (wordToNat x + wordToNat y - x1 * pow2 sz + wordToNat z)
    with (wordToNat x + wordToNat y + wordToNat z - x1 * pow2 sz) by auto.
  replace (wordToNat x + (wordToNat y + wordToNat z - x0 * pow2 sz))
    with (wordToNat x + wordToNat y + wordToNat z - x0 * pow2 sz) by auto.
  repeat rewrite drop_sub; auto.
Qed.
Theorem roundTrip_1 : forall sz, wordToNat (natToWord (S sz) 1) = 1.
Proof.
(* original proof tokens: 15 *)
simpl.
(* No more tactics to try *)
Admitted.

Theorem mod2_WS : forall sz (x : word sz) b, mod2 (wordToNat (WS b x)) = b.
Proof.
(* original proof tokens: 69 *)
unfold wordToNat; destruct b; simpl; auto.
destruct x; simpl; auto; try lia.
destruct b; simpl; auto.
destruct x; simpl; auto; try lia.
destruct b; simpl; auto.
destruct x; simpl; auto; try lia.
destruct b; simpl; auto.
destruct x; simpl; auto; try lia.
(* No more tactics to try *)
Admitted.

Theorem div2_WS : forall sz (x : word sz) b, div2 (wordToNat (WS b x)) = wordToNat x.
Proof.
(* original proof tokens: 40 *)
destruct b; simpl; auto.
rewrite mul2_add; auto.
(* No more tactics to try *)
Admitted.

Theorem wmult_unit_l : forall sz (x : word sz), natToWord sz 1 ^* x = x.
(* hint proof tokens: 90 *)
Proof.
  intros; rewrite wmult_alt; unfold wmultN, wordBinN; intros.
  destruct sz; simpl.
  rewrite (shatter_word x); reflexivity.
  rewrite roundTrip_0; simpl.
  rewrite plus_0_r.
  rewrite (shatter_word x).
  f_equal.

  apply mod2_WS.

  rewrite div2_WS.
  apply natToWord_wordToNat.
Qed.
Theorem wmult_comm : forall sz (x y : word sz), x ^* y = y ^* x.
(* hint proof tokens: 28 *)
Proof.
  intros; repeat rewrite wmult_alt; unfold wmultN, wordBinN; auto with arith.
Qed.
Theorem wmult_unit_r : forall sz (x : word sz), x ^* natToWord sz 1 = x.
(* hint proof tokens: 21 *)
Proof.
  intros.
  rewrite wmult_comm.
  apply wmult_unit_l.
Qed.
Theorem wmult_assoc : forall sz (x y z : word sz), x ^* (y ^* z) = x ^* y ^* z.
(* hint proof tokens: 230 *)
Proof.
  intros; repeat rewrite wmult_alt; unfold wmultN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  rewrite mult_minus_distr_l.
  rewrite mult_minus_distr_r.
  rewrite (mult_assoc (wordToNat x) x0).
  rewrite <- (mult_assoc x1).
  rewrite (mult_comm (pow2 sz)).
  rewrite (mult_assoc x1).
  repeat rewrite drop_sub; auto with arith.
  rewrite (mult_comm x1).
  rewrite <- (mult_assoc (wordToNat x)).
  rewrite (mult_comm (wordToNat y)).
  rewrite mult_assoc.
  rewrite (mult_comm (wordToNat x)).
  repeat rewrite <- mult_assoc.
  auto with arith.
  repeat rewrite <- mult_assoc.
  auto with arith.
Qed.
Theorem wmult_plus_distr : forall sz (x y z : word sz), (x ^+ y) ^* z = (x ^* z) ^+ (y ^* z).
Proof.
(* original proof tokens: 299 *)
intros; repeat rewrite wmult_alt; unfold wmultN, wordBinN; auto with arith.
rewrite wplus_alt.
rewrite wplus_alt.
(* No more tactics to try *)
Admitted.

Theorem wminus_def : forall sz (x y : word sz), x ^- y = x ^+ ^~ y.
(* hint proof tokens: 9 *)
Proof.
  reflexivity.
Qed.
Theorem wordToNat_bound : forall sz (w : word sz), wordToNat w < pow2 sz.
(* hint proof tokens: 21 *)
Proof.
  induction w; simpl; intuition.
  destruct b; simpl; lia.
Qed.
Definition goodSize sz n := n < pow2 sz.
Arguments goodSize : simpl never.
Definition goodSizeEq sz n := n <= pow2 sz.
Arguments goodSizeEq : simpl never.
Theorem wordToNat_good : forall sz (w : word sz), goodSize sz (wordToNat w).
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 12 *)

apply wordToNat_bound.
Qed.

Theorem natToWord_goodSize:
  forall sz (w:word sz),
  goodSize sz (wordToNat w).
Proof.
(* original proof tokens: 59 *)
(* generated proof tokens: 12 *)

apply wordToNat_good.
Qed.

Theorem goodSize_trans: forall sz n1 n2,
  n1 <= n2 -> goodSize sz n2 -> goodSize sz n1.
(* hint proof tokens: 26 *)
Proof.
  intros.
  unfold goodSize in *.
  apply le_lt_trans with n2; lia.
Qed.
Theorem goodSize_word_bound: forall n1 sz (bound: word sz),
  n1 <= wordToNat bound ->
  goodSize sz n1.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Theorem goodSize_bound: forall n1 sz bound,
  n1 <= wordToNat (natToWord sz bound) ->
  goodSize sz n1.
(* hint proof tokens: 19 *)
Proof.
  intros.
  eapply goodSize_word_bound; eauto.
Qed.
Lemma goodSize_sub : forall sz n a,
  goodSize sz n -> goodSize sz (n - a).
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Lemma wordToNat_natToWord_idempotent'_iff : forall n sz,
  @wordToNat sz (natToWord sz n) = n -> goodSize sz n.
(* hint proof tokens: 22 *)
Proof.
  intros.
  eapply goodSize_bound.
  rewrite H.
  auto.
Qed.
Lemma goodSize_add_l : forall sz a b,
  goodSize sz (a + b) -> goodSize sz a.
(* hint proof tokens: 26 *)
Proof.
  intros; eapply goodSize_trans with (n2 := a + b); auto; lia.
Qed.
Lemma goodSize_add_r : forall sz a b,
  goodSize sz (a + b) -> goodSize sz b.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Theorem natToWord_pow2 : forall sz, natToWord sz (pow2 sz) = natToWord sz 0.
(* hint proof tokens: 57 *)
Proof.
  induction sz; simpl; intuition.

  generalize (div2_double (pow2 sz)); simpl; intro Hr; rewrite Hr; clear Hr.
  f_equal.
  generalize (mod2_double (pow2 sz)); auto.
  auto.
Qed.
Theorem wminus_inv : forall sz (x : word sz), x ^+ ^~ x = wzero sz.
(* hint proof tokens: 171 *)
Proof.
  intros; rewrite wneg_alt; rewrite wplus_alt; unfold wnegN, wplusN, wzero, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.
  
  replace (wordToNat x + (pow2 sz - wordToNat x - x0 * pow2 sz))
    with (pow2 sz - x0 * pow2 sz).
  rewrite drop_sub; auto with arith.
  apply natToWord_pow2.
  generalize (wordToNat_bound x).
  lia.
Qed.
Definition wring (sz : nat) : ring_theory (wzero sz) (wone sz) (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz) (@eq _) :=
  mk_rt _ _ _ _ _ _ _
  (@wplus_unit _) (@wplus_comm _) (@wplus_assoc _)
  (@wmult_unit_l _) (@wmult_comm _) (@wmult_assoc _)
  (@wmult_plus_distr _) (@wminus_def _) (@wminus_inv _).
Theorem weqb_sound : forall sz (x y : word sz), weqb x y = true -> x = y.
Proof.
(* original proof tokens: 14 *)
induction x; intros; simpl in *; try congruence.
inversion H; subst; auto; try congruence.
inversion H; subst; auto.
inversion H; subst; auto.
inversion H; subst; auto.
destruct H; try congruence.
inversion H1; subst; auto.
destruct H1; try congruence.
destruct H2; try congruence.
inversion H3; subst; auto.
inversion H3; subst; auto.
inversion H3; subst; auto.
inversion H3; subst; auto.
inversion H3; subst; auto.
(* Reached max number of model calls *)
Admitted.

Arguments weqb_sound : clear implicits.
Ltac is_nat_cst n :=
  match eval hnf in n with
    | O => constr:(true)
    | S ?n' => is_nat_cst n'
    | _ => constr:(false)
  end.
Ltac isWcst w :=
  match eval hnf in w with
    | WO => constr:(true)
    | WS ?b ?w' =>
      match eval hnf in b with
        | true => isWcst w'
        | false => isWcst w'
        | _ => constr:(false)
      end
    | natToWord _ ?n => is_nat_cst n
    | _ => constr:(false)
  end.
Ltac wcst w :=
  let b := isWcst w in
    match b with
      | true => w
      | _ => constr:(NotConstant)
    end.
Ltac noptac x := idtac.
Ltac PackWring sz F :=
  let RNG := (fun proj => proj
    inv_morph_nothing inv_morph_nothing noptac noptac
    (word sz) (@eq (word sz)) (wzero sz) (wone sz)
    (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz)
    (BinNums.Z) (BinNums.N) (id_phi_N)
    (pow_N (wone sz) (@wmult sz))
    (ring_correct (@Eqsth (word sz))
                  (Eq_ext _ _ _)
                  (Rth_ARth (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                  (gen_phiZ_morph (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                  (pow_N_th _ _ (@Eqsth (word sz)))
                  (triv_div_th (@Eqsth (word sz))
                               (Eq_ext _ _ _)
                               (Rth_ARth (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                               (gen_phiZ_morph (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz)))
    )
    tt) in
  F RNG (@nil (word sz)) (@nil (word sz)).
Ltac ring_sz sz := PackWring sz Ring_gen.
Fixpoint wnot sz (w : word sz) : word sz :=
  match w with
    | WO => WO
    | WS b w' => WS (negb b) (wnot w')
  end.
Fixpoint bitwp (f : bool -> bool -> bool) sz (w1 : word sz) : word sz -> word sz :=
  match w1 with
    | WO => fun _ => WO
    | WS b w1' => fun w2 => WS (f b (whd w2)) (bitwp f w1' (wtl w2))
  end.
Fact bitwp_wtl : forall sz (w w' : word (S sz)) op, bitwp op (wtl w) (wtl w') = wtl (bitwp op w w').
(* hint proof tokens: 25 *)
Proof.
  intros.
  rewrite (shatter_word w), (shatter_word w').
  auto.
Qed.
Lemma split1_bitwp_dist : forall sz1 sz2 w w' op,
  split1 sz1 sz2 (bitwp op w w') = bitwp op (split1 sz1 sz2 w) (split1 sz1 sz2 w').
(* hint proof tokens: 53 *)
Proof.
  induction sz1; intros; auto.
  simpl.
  f_equal.
  rewrite (shatter_word w), (shatter_word w'); auto.
  rewrite <- IHsz1, bitwp_wtl.
  reflexivity.
Qed.
Lemma split2_bitwp_dist : forall sz1 sz2 w w' op,
  split2 sz1 sz2 (bitwp op w w') = bitwp op (split2 sz1 sz2 w) (split2 sz1 sz2 w').
Proof.
(* original proof tokens: 32 *)
induction sz1; intros; auto.
simpl.
(* No more tactics to try *)
Admitted.

Lemma combine_bitwp : forall sz1 sz2 (wa wa' : word sz1) (wb wb' : word sz2) op,
  combine (bitwp op wa wa') (bitwp op wb wb') = bitwp op (combine wa wb) (combine wa' wb').
Proof.
(* original proof tokens: 32 *)
induction sz1; intros; simpl.
(* No more tactics to try *)
Admitted.

Lemma eq_rect_bitwp : forall a b Heq f w1 w2,
  bitwp f w1 w2 = eq_rect a word (
    bitwp f (eq_rect b word w1 a Heq) (eq_rect b word w2 a Heq)) b (eq_sym Heq).
(* hint proof tokens: 25 *)
Proof.
  intros a b H; subst a.
  intros; eq_rect_simpl; reflexivity.
Qed.
Fact eq_rect_bitwp' : forall a b Heq f w1 w2,
  eq_rect b word (bitwp f w1 w2) a Heq = bitwp f (eq_rect b word w1 a Heq) (eq_rect b word w2 a Heq).
(* hint proof tokens: 26 *)
Proof.
  intros a b H1; subst a.
  intros; eq_rect_simpl; reflexivity.
Qed.
Fact eq_rect_bitwp_1 : forall a b Heq f w1 w2,
  bitwp f (eq_rect a word w1 b Heq) w2 = eq_rect a word (bitwp f w1 (eq_rect b word w2 a (eq_sym Heq))) b Heq.
Proof.
(* original proof tokens: 24 *)
intros.
rewrite eq_rect_bitwp'.
(* No more tactics to try *)
Admitted.

Definition wnot' sz := bitwp xorb (wones sz).
Theorem wnot_wnot'_equiv : forall sz (w : word sz), wnot w = wnot' w.
Proof.
(* original proof tokens: 21 *)
(* generated proof tokens: 23 *)
induction w; simpl; auto; f_equal.
rewrite IHw.
reflexivity.
Qed.

Theorem wnot_split1 : forall sz1 sz2 w, wnot (split1 sz1 sz2 w) = split1 sz1 sz2 (wnot w).
(* hint proof tokens: 58 *)
Proof.
  intros.
  repeat rewrite wnot_wnot'_equiv.
  unfold wnot'.
  erewrite <- split1_combine with (w := wones _).
  rewrite <- split1_bitwp_dist, combine_wones.
  reflexivity.
Qed.
Theorem wnot_split2 : forall sz1 sz2 w, wnot (split2 sz1 sz2 w) = split2 sz1 sz2 (wnot w).
(* hint proof tokens: 58 *)
Proof.
  intros.
  repeat rewrite wnot_wnot'_equiv.
  unfold wnot'.
  erewrite <- split2_combine with (z := wones _).
  rewrite <- split2_bitwp_dist, combine_wones.
  reflexivity.
Qed.
Theorem wnot_combine : forall sz1 sz2 (w1 : word sz1) (w2 : word sz2),
  wnot (combine w1 w2) = combine (wnot w1) (wnot w2).
(* hint proof tokens: 40 *)
Proof.
  intros.
  repeat rewrite wnot_wnot'_equiv.
  unfold wnot'.
  rewrite <- combine_wones, combine_bitwp.
  reflexivity.
Qed.
Theorem wnot_zero: forall sz, wnot (wzero sz) = wones sz.
(* hint proof tokens: 17 *)
Proof.
  induction sz; simpl; f_equal; eauto.
Qed.
Theorem wnot_ones : forall sz, wnot (wones sz) = wzero sz.
(* hint proof tokens: 22 *)
Proof.
  induction sz; simpl; f_equal; try rewrite IHsz; eauto.
Qed.
Theorem wnot_eq_rect : forall a b H (w : word a), wnot (eq_rect a word w b H) = eq_rect a word (wnot w) b H.
Proof.
(* original proof tokens: 19 *)
intros.
(* No more tactics to try *)
Admitted.

Definition wor := bitwp orb.
Definition wand := bitwp andb.
Definition wxor := bitwp xorb.
Notation "l ^| r" := (@wor _ l%word r%word) (at level 50, left associativity).
Notation "l ^& r" := (@wand _ l%word r%word) (at level 40, left associativity).
Theorem wor_unit : forall sz (x : word sz), wzero sz ^| x = x.
(* hint proof tokens: 22 *)
Proof.
  unfold wzero, wor; induction x; simpl; intuition congruence.
Qed.
Theorem wor_comm : forall sz (x y : word sz), x ^| y = y ^| x.
(* hint proof tokens: 33 *)
Proof.
  unfold wor; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.
Theorem wor_assoc : forall sz (x y z : word sz), x ^| (y ^| z) = x ^| y ^| z.
Proof.
(* original proof tokens: 33 *)
(* generated proof tokens: 39 *)

unfold wor; induction x; intros; rewrite (shatter_word y), (shatter_word z); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_unit : forall sz (x : word sz), wones sz ^& x = x.
Proof.
(* original proof tokens: 19 *)
(* generated proof tokens: 27 *)

unfold wand, wones; induction x; simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_kill : forall sz (x : word sz), wzero sz ^& x = wzero sz.
Proof.
(* original proof tokens: 22 *)
(* generated proof tokens: 27 *)

unfold wand, wzero; induction x; simpl; auto; f_equal; auto with bool.
Qed.

Theorem wand_comm : forall sz (x y : word sz), x ^& y = y ^& x.
(* hint proof tokens: 33 *)
Proof.
  unfold wand; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.
Theorem wand_assoc : forall sz (x y z : word sz), x ^& (y ^& z) = x ^& y ^& z.
Proof.
(* original proof tokens: 33 *)
(* generated proof tokens: 39 *)

unfold wand; induction x; intros; rewrite (shatter_word y), (shatter_word z); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_or_distr : forall sz (x y z : word sz), (x ^| y) ^& z = (x ^& z) ^| (y ^& z).
Proof.
(* original proof tokens: 64 *)
intros.
unfold wor, wand, bitwp; simpl; f_equal; auto with bool.
(* No more tactics to try *)
Admitted.

Lemma wor_wones : forall sz w, wones sz ^| w = wones sz.
Proof.
(* original proof tokens: 25 *)
(* generated proof tokens: 21 *)

unfold wor; induction w; simpl; auto; congruence.
Qed.

Lemma wor_wzero : forall sz w, wzero sz ^| w = w.
Proof.
(* original proof tokens: 16 *)
(* generated proof tokens: 24 *)

unfold wor, wzero; induction w; simpl; auto; congruence.
Qed.

Lemma wand_wones : forall sz w, wones sz ^& w = w.
(* hint proof tokens: 16 *)
Proof.
  unfold wand; induction sz; shatterer.
Qed.
Lemma wand_wzero : forall sz w, wzero sz ^& w = wzero sz.
(* hint proof tokens: 26 *)
Proof.
  intros. rewrite <- wzero'_def.
  unfold wand; induction sz; shatterer.
Qed.
Lemma wxor_wones : forall sz w, wxor (wones sz) w = wnot w.
Proof.
(* original proof tokens: 17 *)
(* generated proof tokens: 26 *)

unfold wxor, wnot; induction w; simpl; auto; f_equal; auto.
Qed.

Lemma wxor_wzero : forall sz w, wxor (wzero sz) w = w.
(* hint proof tokens: 25 *)
Proof.
  unfold wxor; induction sz; shatterer; destruct (whd w); auto.
Qed.
Lemma wxor_comm : forall sz (w1 w2 : word sz), wxor w1 w2 = wxor w2 w1.
(* hint proof tokens: 51 *)
Proof.
  unfold wxor; induction sz. shatterer.
  intros. rewrite (shatter_word w1), (shatter_word w2).
  simpl.
  rewrite xorb_comm, IHsz.
  reflexivity.
Qed.
Lemma wxor_assoc : forall sz (w1 w2 w3 : word sz), wxor w1 (wxor w2 w3) = wxor (wxor w1 w2) w3.
(* hint proof tokens: 64 *)
Proof.
  unfold wxor.
  induction sz; intros; rewrite (shatter_word w1), (shatter_word w2), (shatter_word w3); auto.
  simpl; f_equal.
  rewrite xorb_assoc_reverse; auto.
  rewrite IHsz.
  reflexivity.
Qed.
Lemma wor_wone : forall sz (w : word sz) b,
  WS b w ^| wone _ = WS true w.
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

Lemma wand_wone : forall sz (w : word sz) b,
  WS b w ^& wone _ = WS b (wzero _).
(* hint proof tokens: 62 *)
Proof.
  intros.
  compute [wone natToWord wand]. simpl.
  fold natToWord.
  change (natToWord sz 0) with (wzero sz).
  rewrite andb_true_r.
  rewrite wand_comm, wand_wzero.
  reflexivity.
Qed.
Lemma wxor_wone : forall sz (w : word sz) b,
  wxor (WS b w) (wone _) = WS (negb b) w.
(* hint proof tokens: 65 *)
Proof.
  intros.
  compute [wone natToWord wxor]. simpl.
  fold natToWord.
  change (natToWord sz 0) with (wzero sz).
  rewrite xorb_true_r.
  rewrite wxor_comm, wxor_wzero.
  reflexivity.
Qed.
Definition wbring (sz : nat) : semi_ring_theory (wzero sz) (wones sz) (@wor sz) (@wand sz) (@eq _) :=
  mk_srt _ _ _ _ _
  (@wor_unit _) (@wor_comm _) (@wor_assoc _)
  (@wand_unit _) (@wand_kill _) (@wand_comm _) (@wand_assoc _)
  (@wand_or_distr _).
Ltac word_simpl := unfold sext, zext, wzero in *; simpl in *.
Ltac word_eq := ring.
Ltac word_eq1 := match goal with
                   | _ => ring
                   | [ H : _ = _ |- _ ] => ring [H]
                 end.
Theorem word_neq : forall sz (w1 w2 : word sz),
  w1 ^- w2 <> wzero sz
  -> w1 <> w2.
Proof.
(* original proof tokens: 31 *)
intros.
unfold wminus in H.
(* No more tactics to try *)
Admitted.

Ltac word_neq := apply word_neq; let H := fresh "H" in intro H; simpl in H; ring_simplify in H; try discriminate.
Ltac word_contra := match goal with 
                      | [ H : _ <> _ |- False ] => apply H; ring
                    end.
Ltac word_contra1 := match goal with 
                       | [ H : _ <> _ |- False ] => apply H;
                         match goal with
                           | _ => ring
                           | [ H' : _ = _ |- _ ] => ring [H']
                         end
                     end.
Open Scope word_scope.
Definition wordToZ sz (w : word sz) : Z :=
  if wmsb w true then 
    
    match wordToN (wneg w) with
      | N0 => Z0
      | Npos x => Zneg x
    end
  else 
    
    match wordToN w with
      | N0 => Z0
      | Npos x => Zpos x
    end.
Definition wlt sz (l r : word sz) : Prop :=
  N.lt (wordToN l) (wordToN r).
Definition wslt sz (l r : word sz) : Prop :=
  BinInt.Z.lt (wordToZ l) (wordToZ r).
Notation "w1 > w2" := (@wlt _ w2%word w1%word) : word_scope.
Notation "w1 >= w2" := (~(@wlt _ w1%word w2%word)) : word_scope.
Notation "w1 < w2" := (@wlt _ w1%word w2%word) : word_scope.
Notation "w1 <= w2" := (~(@wlt _ w2%word w1%word)) : word_scope.
Notation "w1 '>s' w2" := (@wslt _ w2%word w1%word) (at level 70, w2 at next level) : word_scope.
Notation "w1 '>s=' w2" := (~(@wslt _ w1%word w2%word)) (at level 70, w2 at next level) : word_scope.
Notation "w1 '<s' w2" := (@wslt _ w1%word w2%word) (at level 70, w2 at next level) : word_scope.
Notation "w1 '<s=' w2" := (~(@wslt _ w2%word w1%word)) (at level 70, w2 at next level) : word_scope.
Definition wlt_dec : forall sz (l r : word sz), {l < r} + {l >= r}.
refine (fun sz l r => 
    match N.compare (wordToN l) (wordToN r) as k return N.compare (wordToN l) (wordToN r) = k -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.
Defined.
Definition wslt_dec : forall sz (l r : word sz), {l <s r} + {l >s= r}.
refine (fun sz l r => 
    match BinInt.Z.compare (wordToZ l) (wordToZ r) as c return BinInt.Z.compare (wordToZ l) (wordToZ r) = c -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.
Defined.
Lemma not_wlt_ge : forall sz (l r : word sz),
  ((l < r) -> False) -> (r <= l).
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Lemma not_wle_gt : forall sz (l r : word sz),
  ((l <= r) -> False) -> (r < l).
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Lemma lt_le : forall sz (a b : word sz),
  a < b -> a <= b.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma eq_le : forall sz (a b : word sz),
  a = b -> a <= b.
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Lemma wordToN_inj : forall sz (a b : word sz),
  wordToN a = wordToN b -> a = b.
(* hint proof tokens: 179 *)
Proof.
  induction a; intro b0; rewrite (shatter_word b0); intuition.
  destruct b; destruct (whd b0); intros; unfold wordToN in H; fold wordToN in H.
  f_equal. eapply IHa. eapply N.succ_inj in H.
  destruct (wordToN a); destruct (wordToN (wtl b0)); simpl in H; try congruence.
  destruct (wordToN (wtl b0)); destruct (wordToN a); inversion H.
  destruct (wordToN (wtl b0)); destruct (wordToN a); inversion H.
  f_equal. eapply IHa. 
  destruct (wordToN a); destruct (wordToN (wtl b0)); simpl in *; try congruence.
Qed.
Lemma wordToNat_inj : forall sz (a b : word sz),
  wordToNat a = wordToNat b -> a = b.
Proof.
(* original proof tokens: 35 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma unique_inverse : forall sz (a b1 b2 : word sz),
  a ^+ b1 = wzero _ ->
  a ^+ b2 = wzero _ ->
  b1 = b2.
(* hint proof tokens: 77 *)
Proof.
  intros.
  transitivity (b1 ^+ wzero _).
  rewrite wplus_comm. rewrite wplus_unit. auto.
  transitivity (b1 ^+ (a ^+ b2)). congruence.
  rewrite wplus_assoc.
  rewrite (wplus_comm b1). rewrite H. rewrite wplus_unit. auto.
Qed.
Lemma sub_0_eq : forall sz (a b : word sz),
  a ^- b = wzero _ -> a = b.
(* hint proof tokens: 134 *)
Proof.
  intros. destruct (weq (wneg b) (wneg a)).
  transitivity (a ^+ (^~ b ^+ b)).
  rewrite (wplus_comm (^~ b)). rewrite wminus_inv. 
  rewrite wplus_comm. rewrite wplus_unit. auto.
  rewrite e. rewrite wplus_assoc. rewrite wminus_inv. rewrite wplus_unit. auto.
  unfold wminus in H.
  generalize (unique_inverse a (wneg a) (^~ b)).
  intros. elimtype False. apply n. symmetry; apply H0.
  apply wminus_inv.
  auto.
Qed.
Lemma le_neq_lt : forall sz (a b : word sz),
  b <= a -> a <> b -> b < a.
(* hint proof tokens: 102 *)
Proof.
  intros; destruct (wlt_dec b a); auto.
  elimtype False. apply H0. unfold wlt, N.lt in *.
  eapply wordToN_inj. eapply Ncompare_eq_correct.
  case_eq ((wordToN a ?= wordToN b)%N); auto; try congruence.
  intros. rewrite <- Ncompare_antisym in n. rewrite H1 in n. simpl in *. congruence.
Qed.
Hint Resolve word_neq lt_le eq_le sub_0_eq le_neq_lt : worder.
Ltac shatter_word x :=
  match type of x with
    | word 0 => try rewrite (shatter_word_0 x) in *
    | word (S ?N) => 
      let x' := fresh in 
      let H := fresh in
      destruct (@shatter_word_S N x) as [ ? [ x' H ] ];
      rewrite H in *; clear H; shatter_word x'
  end.
Lemma rewrite_weq : forall sz (a b : word sz)
  (pf : a = b),  
  weq a b = left _ pf.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma natToWord_plus : forall sz n m, natToWord sz (n + m) = natToWord _ n ^+ natToWord _ m.
(* hint proof tokens: 140 *)
Proof.
  destruct sz; intuition.
  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  destruct (wordToNat_natToWord (S sz) n); intuition.
  destruct (wordToNat_natToWord (S sz) m); intuition.
  rewrite H0; rewrite H2; clear H0 H2.
  replace (n - x * pow2 (S sz) + (m - x0 * pow2 (S sz))) with (n + m - x * pow2 (S sz) - x0 * pow2 (S sz))
    by lia.
  repeat rewrite drop_sub; auto; lia.
Qed.
Lemma natToWord_S : forall sz n, natToWord sz (S n) = natToWord _ 1 ^+ natToWord _ n.
(* hint proof tokens: 25 *)
Proof.
  intros; change (S n) with (1 + n); apply natToWord_plus.
Qed.
Theorem natToWord_inj : forall sz n m, natToWord sz n = natToWord sz m
  -> goodSize sz n
  -> goodSize sz m
  -> n = m.
Proof.
(* original proof tokens: 106 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma wordToNat_natToWord_idempotent : forall sz n,
  (N.of_nat n < Npow2 sz)%N
  -> wordToNat (natToWord sz n) = n.
(* hint proof tokens: 79 *)
Proof.
  intros.
  destruct (wordToNat_natToWord sz n); intuition.
  destruct x.
  simpl in *; lia.
  simpl in *.
  apply Nlt_out in H.
  autorewrite with N in *.
  rewrite Npow2_nat in *.
  generalize dependent (x * pow2 sz).
  intros; lia.
Qed.
Lemma wplus_cancel : forall sz (a b c : word sz),
  a ^+ c = b ^+ c
  -> a = b.
(* hint proof tokens: 73 *)
Proof.
  intros.
  apply (f_equal (fun x => x ^+ ^~ c)) in H.
  repeat rewrite <- wplus_assoc in H.
  rewrite wminus_inv in H.
  repeat rewrite (wplus_comm _ (wzero sz)) in H.
  repeat rewrite wplus_unit in H.
  assumption.
Qed.
Lemma natToWord_mult : forall sz n m, natToWord sz (n * m) = natToWord _ n ^* natToWord _ m.
(* hint proof tokens: 264 *)
Proof.
  destruct sz; intuition.
  rewrite wmult_alt.
  unfold wmultN, wordBinN.
  destruct (wordToNat_natToWord (S sz) n); intuition.
  destruct (wordToNat_natToWord (S sz) m); intuition.
  rewrite H0; rewrite H2; clear H0 H2.
  replace ((n - x * pow2 (S sz)) * (m - x0 * pow2 (S sz)))
    with ((n - x * pow2 (S sz)) * m - (n - x * pow2 (S sz)) * (x0 * pow2 (S sz)))
    by (rewrite Nat.mul_sub_distr_l; auto).
  rewrite mult_assoc; rewrite drop_sub.
  repeat rewrite mult_comm with (m:=m).
  replace (m * (n - x * pow2 (S sz)))
    with (m * n - m * (x * pow2 (S sz)))
    by (rewrite Nat.mul_sub_distr_l; auto).
  rewrite mult_assoc; rewrite drop_sub.
  auto.
  rewrite <- mult_assoc; apply Nat.mul_le_mono_l; auto.
  rewrite <- mult_assoc; apply Nat.mul_le_mono_l; auto.
Qed.
Lemma wlt_lt: forall sz (a b : word sz), a < b ->
  (wordToNat a < wordToNat b)%nat.
(* hint proof tokens: 46 *)
Proof.
  intros.
  unfold wlt in H.
  repeat rewrite wordToN_nat in *.
  apply Nlt_out in H.
  repeat rewrite Nat2N.id in *.
  auto.
Qed.
Lemma wle_le: forall sz (a b : word sz), (a <= b)%word ->
  (wordToNat a <= wordToNat b)%nat.
(* hint proof tokens: 46 *)
Proof.
  intros.
  unfold wlt in H.
  repeat rewrite wordToN_nat in *.
  apply Nge_out in H.
  repeat rewrite Nat2N.id in *.
  auto.
Qed.
Lemma wlt_lt': forall sz a b, goodSize sz a
  -> natToWord sz a < b
  -> (wordToNat (natToWord sz a) < wordToNat b)%nat.
(* hint proof tokens: 17 *)
Proof.
  intros.
  apply wlt_lt.
  auto.
Qed.
Lemma lt_word_lt_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n < (natToWord sz m))%word ->
  (wordToNat n < m)%nat.
Proof.
(* original proof tokens: 53 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma le_word_le_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n <= (natToWord sz m))%word ->
  (wordToNat n <= m)%nat.
Proof.
(* original proof tokens: 53 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma lt_word_le_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n < (natToWord sz m))%word ->
  (wordToNat n <= m)%nat.
Proof.
(* original proof tokens: 28 *)
intros.
apply wlt_lt in H.
(* No more tactics to try *)
Admitted.

Hint Resolve lt_word_le_nat.
Lemma wordToNat_natToWord_idempotent' : forall sz n,
  goodSize sz n
  -> wordToNat (natToWord sz n) = n.
(* hint proof tokens: 59 *)
Proof.
  unfold goodSize.
  intros.
  destruct (wordToNat_natToWord sz n); intuition.
  destruct x.
  simpl in *; lia.
  simpl in *.
  generalize dependent (x * pow2 sz).
  intros; lia.
Qed.
Lemma le_word_le_nat': forall (sz:nat) n m,
  goodSize sz n ->
  (natToWord sz n <= m)%word ->
  (n <= wordToNat m)%nat.
Proof.
(* original proof tokens: 35 *)
(* generated proof tokens: 39 *)

intros.
apply wle_le in H0.
rewrite wordToNat_natToWord_idempotent' in H0;[|apply H].
auto.
Qed.

Lemma wordToNat_natToWord_bound : forall sz n (bound : word sz),
  (n <= wordToNat bound)%nat
  -> wordToNat (natToWord sz n) = n.
(* hint proof tokens: 37 *)
Proof.
  intros.
  apply wordToNat_natToWord_idempotent'.
  eapply le_lt_trans; eauto.
  apply wordToNat_bound.
Qed.
Lemma wordToNat_natToWord_le : forall sz n,
  (wordToNat (natToWord sz n) <= n)%nat.
Proof.
(* original proof tokens: 60 *)
induction n; simpl; auto.
rewrite roundTrip_0; auto.
rewrite Nat.add_le_mono_r.
rewrite Nat.add_le_mono_r.
apply Nat.le_succ_r.
rewrite plus_n_Sm.
rewrite Nat.add_succ_r.
(* No more tactics to try *)
Admitted.

Lemma wordToNat_natToWord_lt : forall sz n b,
  (n < b -> wordToNat (natToWord sz n) < b)%nat.
(* hint proof tokens: 28 *)
Proof.
  intros.
  eapply le_lt_trans.
  apply wordToNat_natToWord_le.
  auto.
Qed.
Lemma wordToNat_eq_natToWord : forall sz (w : word sz) n,
  wordToNat w = n
  -> w = natToWord sz n.
(* hint proof tokens: 22 *)
Proof.
  intros. rewrite <- H. rewrite natToWord_wordToNat. auto.
Qed.
Lemma wlt_lt_bound: forall sz (a : word sz) (b bound : nat),
  (a < natToWord sz b)%word
  -> (b <= wordToNat (natToWord sz bound))%nat
  -> (wordToNat a < b)%nat.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma natplus1_wordplus1_eq:
  forall sz (a bound : word sz),
    (0 < sz)%nat ->
    (a < bound)%word ->
    (wordToNat a) + 1 = wordToNat (a ^+ (natToWord sz 1)).
Proof.
(* original proof tokens: 118 *)
intros.
rewrite wplus_alt;unfold wplusN;unfold wordBinN;unfold plus.
rewrite wordToNat_natToWord_idempotent'.
rewrite Nat.add_1_r.
(* No more tactics to try *)
Admitted.

Lemma lt_wlt: forall sz (n : word sz) m, (wordToNat n < wordToNat m)%nat ->
  n < m.
(* hint proof tokens: 38 *)
Proof.
  intros.
  unfold wlt.
  repeat rewrite wordToN_nat.
  apply Nlt_in.
  repeat rewrite Nat2N.id.
  auto.
Qed.
Lemma le_wle: forall sz (n : word sz) m, (wordToNat n <= wordToNat m)%nat ->
  n <= m.
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Lemma wlt_wle_incl : forall sz (a b : word sz),
  (a < b)%word -> (a <= b)%word.
(* hint proof tokens: 25 *)
Proof.
  intros.
  apply wlt_lt in H.
  apply le_wle.
  lia.
Qed.
Lemma wminus_Alt2: forall sz x y, y <= x ->
  @wminusN sz x y = wordBinN minus x y.
(* hint proof tokens: 413 *)
Proof.
  intros.
  unfold wminusN, wplusN, wnegN, wordBinN.
  destruct (weq y (natToWord sz 0)); subst.

  rewrite roundTrip_0.
  repeat rewrite <- minus_n_O.
  rewrite <- drop_sub with (k:=1) (n:=pow2 sz); try lia.
  replace (pow2 sz - 1 * pow2 sz) with (0) by lia.
  rewrite roundTrip_0.
  rewrite <- plus_n_O.
  reflexivity.

  rewrite wordToNat_natToWord_idempotent' with (n:=pow2 sz - wordToNat y).
  rewrite <- drop_sub with (k:=1).
  simpl.
  rewrite <- plus_n_O.
  replace (wordToNat x + (pow2 sz - wordToNat y) - pow2 sz) with (wordToNat x - wordToNat y).
  auto.
  rewrite Nat.add_sub_assoc.
  lia.

  remember (wordToNat_bound y); lia.

  simpl. rewrite <- plus_n_O.
  rewrite Nat.add_sub_assoc; [| remember (wordToNat_bound y); lia ].
  rewrite plus_comm.
  rewrite <- Nat.add_sub_assoc.
  lia.

  apply Nat.nlt_ge.
  unfold not in *; intros.
  apply H.
  apply lt_wlt; auto.

  apply Nat.sub_lt.
  remember (wordToNat_bound y); lia.

  assert (wordToNat y <> 0); try lia.

  assert (wordToN y <> wordToN (natToWord sz 0)).
  unfold not in *. intros. apply n.
  apply wordToN_inj.
  auto.

  repeat rewrite wordToN_nat in H0.
  unfold not in *. intros. apply H0.
  apply N2Nat.inj.
  repeat rewrite Nat2N.id.
  rewrite roundTrip_0.
  auto.
Qed.
Theorem wlt_wf:
  forall sz, well_founded (@wlt sz).
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Ltac wlt_ind :=
  match goal with
  | [ |- forall (n: word ?len), ?P ] =>
    refine (well_founded_ind (@wlt_wf len) (fun n => P) _)
  end.
Theorem wordToNat_plusone: forall sz w w', w < w' ->
  wordToNat (w ^+ natToWord sz 1) = S (wordToNat w).
(* hint proof tokens: 157 *)
Proof.
  intros.

  destruct sz.
  exfalso.
  rewrite word0 with (w:=w') in H.
  rewrite word0 with (w:=w) in H.
  apply wlt_lt in H.
  lia.

  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  rewrite wordToNat_natToWord_idempotent'.

  rewrite roundTrip_1.
  lia.

  eapply Nat.le_lt_trans; [| apply wordToNat_bound ].
  rewrite wordToNat_natToWord_idempotent';
    [| erewrite <- roundTrip_1; apply wordToNat_bound ].
  apply wlt_lt in H.
  instantiate (1:=w').
  lia.
Qed.
Theorem wordToNat_minus_one': forall sz n, n <> natToWord sz 0 ->
  S (wordToNat (n ^- natToWord sz 1)) = wordToNat n.
Proof.
(* original proof tokens: 230 *)
intros.
unfold wminus.
(* No more tactics to try *)
Admitted.

Theorem wordToNat_minus_one: forall sz n, n <> natToWord sz 0 ->
  wordToNat (n ^- natToWord sz 1) = wordToNat n - 1.
Proof.
(* original proof tokens: 97 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma lt_minus : forall a b c,
  (b <= a -> b < c -> a < c -> a - b < c)%nat.
(* hint proof tokens: 10 *)
Proof.
  intros; lia.
Qed.
Lemma wminus_minus : forall sz (a b : word sz),
  b <= a
  -> wordToNat (a ^- b) = wordToNat a - wordToNat b.
Proof.
(* original proof tokens: 76 *)

(* No more tactics to try *)
Admitted.

Lemma wordToNat_neq_inj: forall sz (a b : word sz),
  a <> b <-> wordToNat a <> wordToNat b.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma natToWord_discriminate: forall sz, (sz > 0)%nat -> natToWord sz 0 <> natToWord sz 1.
(* hint proof tokens: 41 *)
Proof.
  unfold not.
  intros.
  induction sz.
  lia.
  unfold natToWord in H0; fold natToWord in H0.
  discriminate H0.
Qed.
Notation "$ n" := (natToWord _ n) (at level 0).
Notation "# n" := (wordToNat n) (at level 0).
Definition bit_dec : forall (a : word 1), {a = $0} + {a = $1}.
intro.
rewrite (shatter_word a).
replace (wtl a) with WO by auto.
destruct (whd a).
right; apply eq_refl.
left; apply eq_refl.
Defined.
Lemma neq0_wneq0: forall sz (n : word sz),
  wordToNat n <> 0  <-> n <> $0.
Proof.
(* original proof tokens: 52 *)
unfold not; split; intros; subst; auto.
(* No more tactics to try *)
Admitted.

Lemma gt0_wneq0: forall sz (n : word sz),
  (wordToNat n > 0)%nat <-> n <> $0.
(* hint proof tokens: 43 *)
Proof.
  split; intros.
  apply neq0_wneq0; lia.
  apply wordToNat_neq_inj in H.
  rewrite roundTrip_0 in H; lia.
Qed.
Lemma weq_minus1_wlt: forall sz (a b : word sz),
  (a <> $0 -> a ^- $1 = b -> a > b)%word.
(* hint proof tokens: 39 *)
Proof.
  intros.
  apply lt_wlt; subst.
  rewrite wordToNat_minus_one; auto.
  apply gt0_wneq0 in H.
  lia.
Qed.
Lemma wordnat_minus1_eq : forall sz n (w : word sz),
  (n > 0)%nat
  -> n = wordToNat w
  -> n - 1 = wordToNat (w ^- $1).
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma sz_minus_nshift : forall sz nshift, (nshift < sz)%nat -> sz = sz - nshift + nshift.
(* hint proof tokens: 10 *)
Proof.
  intros; lia.
Qed.
Lemma nshift_plus_nkeep : forall sz nshift, (nshift < sz)%nat -> nshift + (sz - nshift) = sz.
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 8 *)

lia.
Qed.

Definition wlshift (sz : nat) (w : word sz) (n : nat) : word sz.
refine (split1 sz n _).
rewrite plus_comm.
exact (combine (wzero n) w).
Defined.
Definition wrshift (sz : nat) (w : word sz) (n : nat) : word sz.
refine (split2 n sz _).
rewrite plus_comm.
exact (combine w (wzero n)).
Defined.
Notation "l ^<< r" := (@wlshift _ _ l%word r%word) (at level 35).
Notation "l ^>> r" := (@wrshift _ _ l%word r%word) (at level 35).
Theorem wlshift_0 : forall sz (w : word sz), @wlshift sz w 0 = w.
Proof.
(* original proof tokens: 21 *)
unfold wlshift; simpl.
(* No more tactics to try *)
Admitted.

Theorem wrshift_0 : forall sz (w : word sz), @wrshift sz w 0 = w.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Theorem wlshift_gt : forall sz n (w : word sz), (n > sz)%nat ->
  wlshift w n = wzero sz.
Proof.
(* original proof tokens: 97 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem wrshift_gt : forall sz n (w : word sz), (n > sz)%nat ->
  wrshift w n = wzero sz.
Proof.
(* original proof tokens: 119 *)
unfold wrshift; intros.
(* No more tactics to try *)
Admitted.

Theorem wlshift_bitwp : forall sz (w1 w2 : word sz) f n,
  wlshift (bitwp f w1 w2) n = split1 sz n (
    eq_rec _ word (combine (wzero n) (bitwp f w1 w2)) _ (eq_sym (Nat.add_comm sz n))).
(* hint proof tokens: 23 *)
Proof.
  intros.
  unfold wlshift.
  eq_rect_simpl.
  reflexivity.
Qed.
Theorem wrshift_bitwp : forall sz (w1 w2 : word sz) f n,
  wrshift (bitwp f w1 w2) n = split2 n sz (
    eq_rect _ word (combine (bitwp f w1 w2) (wzero n)) _ (eq_sym (Nat.add_comm n sz))).
(* hint proof tokens: 23 *)
Proof.
  intros.
  unfold wrshift.
  eq_rect_simpl.
  reflexivity.
Qed.
Theorem wnot_wlshift : forall sz (w : word sz) n,
  wnot (wlshift w n) = split1 sz n (eq_rect _ word (combine (wones n) (wnot w)) _ (eq_sym (Nat.add_comm sz n))).
(* hint proof tokens: 50 *)
Proof.
  intros.
  unfold wlshift.
  rewrite wnot_split1.
  eq_rect_simpl.
  rewrite wnot_eq_rect.
  rewrite wnot_combine.
  rewrite wnot_zero.
  reflexivity.
Qed.
Theorem wnot_wrshift : forall sz (w : word sz) n,
  wnot (wrshift w n) = split2 n sz (eq_rect _ word (combine (wnot w) (wones n)) _ (eq_sym (Nat.add_comm n sz))).
(* hint proof tokens: 50 *)
Proof.
  intros.
  unfold wrshift.
  rewrite wnot_split2.
  eq_rect_simpl.
  rewrite wnot_eq_rect.
  rewrite wnot_combine.
  rewrite wnot_zero.
  reflexivity.
Qed.
Definition wbit sz sz' (n : word sz') := natToWord sz (pow2 (wordToNat n)).
Theorem div2_pow2_twice: forall n,
  Nat.div2 (pow2 n + (pow2 n + 0)) = pow2 n.
(* hint proof tokens: 44 *)
Proof.
  intros.
  replace (pow2 n + (pow2 n + 0)) with (2 * pow2 n) by lia.
  rewrite Nat.div2_double.
  auto.
Qed.
Theorem zero_or_wordToNat_S: forall sz (n : word sz),
  n = $0 \/
  exists nn, wordToNat n = S nn /\ wordToNat (n ^- $1) = nn.
Proof.
(* original proof tokens: 210 *)
destruct n; auto.
right; exists (wordToNat n0); split; [| rewrite wordToNat_minus_one; auto ].
intros.
destruct b; simpl; try lia.
(* No more tactics to try *)
Admitted.

Theorem wbit_or_same : forall sz sz' (n : word sz'), (wordToNat n < sz)%nat
  -> (wbit sz n) ^| (wbit sz n) <> wzero sz.
Proof.
(* original proof tokens: 130 *)
unfold wbit, wor.
intros.
(* No more tactics to try *)
Admitted.

Theorem mod2_pow2_twice: forall n,
  mod2 (pow2 n + (pow2 n + 0)) = false.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Theorem wbit_or_other : forall sz sz' (n1 n2 : word sz'), (wordToNat n1 < sz)%nat
  -> (wordToNat n2 < sz)%nat
  -> (n1 <> n2)
  -> (wbit sz n1) ^& (wbit sz n2) = wzero sz.
(* hint proof tokens: 213 *)
Proof.
  induction sz; intros; try lia.
  unfold wbit, wzero, wand.
  simpl.
  destruct (zero_or_wordToNat_S n1); destruct (zero_or_wordToNat_S n2);
    try congruence; destruct_conjs; subst; try rewrite roundTrip_0.

  repeat rewrite H4; simpl; repeat rewrite mod2_pow2_twice; f_equal.
  rewrite wand_kill; auto.

  repeat rewrite H4; simpl; repeat rewrite mod2_pow2_twice; f_equal.
  rewrite wand_comm; rewrite wand_kill; auto.

  repeat rewrite H4; repeat rewrite H6; simpl.
  repeat rewrite mod2_pow2_twice; f_equal.
  repeat rewrite div2_pow2_twice.
  eapply IHsz; try lia.

  apply word_neq.
  unfold not in *; intros; apply H1; clear H1.
  apply sub_0_eq; rewrite <- H2.
  ring_sz sz'.
Qed.
Theorem wbit_and_not: forall sz sz' (n : word sz'), (wordToNat n < sz)%nat
  -> (wbit sz n) ^& wnot (wbit sz n) = wzero sz.
Proof.
(* original proof tokens: 114 *)
unfold wbit, wzero, wand, wnot; simpl; intros.
rewrite wnot_wnot'_equiv.
(* No more tactics to try *)
Admitted.

Theorem wbit_and_not_other: forall sz sz' (n1 n2 : word sz'), (wordToNat n1 < sz)%nat
  -> (wordToNat n2 < sz)%nat
  -> n1 <> n2
  -> (wbit sz n1) ^& wnot (wbit sz n2) = wbit sz n1.
(* hint proof tokens: 253 *)
Proof.
  induction sz; intros; try lia.
  unfold wbit, wzero, wand, wnot.
  simpl.
  destruct (zero_or_wordToNat_S n1); destruct (zero_or_wordToNat_S n2);
    try congruence; destruct_conjs; subst; fold wnot; try rewrite roundTrip_0; simpl;
    f_equal.

  rewrite H4; simpl; rewrite mod2_pow2_twice; auto.
  rewrite H4; simpl; rewrite div2_pow2_twice; apply wand_kill.

  rewrite H4; simpl; rewrite mod2_pow2_twice; auto.
  rewrite H4; simpl; rewrite div2_pow2_twice.
  rewrite wnot_zero. rewrite wand_comm. apply wand_unit.

  rewrite H4; simpl; rewrite mod2_pow2_twice; simpl; apply andb_true_r.
  rewrite H4; rewrite H6; simpl.
  repeat rewrite div2_pow2_twice.
  apply IHsz; try lia.

  apply word_neq.
  unfold not in *; intros; apply H1.
  apply sub_0_eq.
  rewrite <- H2.
  ring_sz sz'.
Qed.
Close Scope word_scope.
Arguments natToWord : simpl never.
Arguments weq : simpl never.
Global Opaque wlt_dec.
Definition test_wlt_f (a : nat) (b : nat) : nat :=
  if wlt_dec (natToWord 64 a) $0 then 0 else 0.
Theorem test_wlt_f_example: forall x y z, test_wlt_f x y = 0 -> test_wlt_f x z = 0.
(* hint proof tokens: 12 *)
Proof.
  intros.
  exact H.
Qed.
