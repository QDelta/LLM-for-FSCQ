Require Import Ascii String Lia OrderedTypeEx.
Import PeanoNat.
Lemma nat_compare_eq_refl : forall x, Nat.compare x x = Eq.
intros; apply Nat.compare_eq_iff; trivial.
Qed.
Hint Rewrite <- Compare_dec.nat_compare_lt : nat_comp_hints.
Hint Rewrite <- Compare_dec.nat_compare_gt : nat_comp_hints.
Hint Rewrite    Nat.compare_eq_iff : nat_comp_hints.
Hint Rewrite <- Nat.compare_eq_iff : nat_comp_hints.
Hint Rewrite    nat_compare_eq_refl : nat_comp_hints.
Ltac autorewrite_nat_compare :=
  autorewrite with nat_comp_hints in *.
Lemma nat_compare_consistent :
  forall n0 n1,
    { Nat.compare n0 n1 = Lt /\ Nat.compare n1 n0 = Gt }
    + { Nat.compare n0 n1 = Eq /\ Nat.compare n1 n0 = Eq }
    + { Nat.compare n0 n1 = Gt /\ Nat.compare n1 n0 = Lt }.
Proof.
  intros n0 n1;
  destruct (Compare_dec.lt_eq_lt_dec n0 n1) as [ [_lt | _eq] | _lt ];
  [ constructor 1; constructor 1  | constructor 1; constructor 2 | constructor 2 ];
  split;
  autorewrite_nat_compare;
  intuition.
Qed.
Module String_as_OT <: UsualOrderedType.
Definition t := string.
Fixpoint string_compare str1 str2 :=
    match str1, str2 with
      | EmptyString, EmptyString => Eq
      | EmptyString, _           => Lt
      | _, EmptyString           => Gt
      | String char1 tail1, String char2 tail2 =>
        match Nat.compare (nat_of_ascii char1) (nat_of_ascii char2) with
          | Eq => string_compare tail1 tail2
          | Lt => Lt
          | Gt => Gt
        end
    end.
Lemma string_compare_eq_refl : forall x, string_compare x x = Eq.
intro x;
    induction x;
      simpl; trivial;
      autorewrite_nat_compare.
trivial.
Qed.
Ltac comparisons_minicrush :=
    autorewrite_nat_compare;
    match goal with
      | [ |- context [Nat.compare ?a ?b] ] =>
        let H := fresh in
        first [
            assert (Nat.compare a b = Eq) as H by (autorewrite_nat_compare; lia) |
            assert (Nat.compare a b = Lt) as H by (autorewrite_nat_compare; lia) |
            assert (Nat.compare a b = Gt) as H by (autorewrite_nat_compare; lia)
        ]; rewrite H; intuition
    end.
Ltac destruct_comparisons :=
    repeat match goal with
             | [ H: match ?pred ?a ?b with
                      | Lt => _ | Gt => _ | Eq => _ end = _
                 |- _] =>
               let H := fresh in
               destruct (pred a b) eqn:H;
                 try discriminate
           end.
Ltac exfalso_from_equalities :=
    match goal with
      | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] => assert (b = c) by congruence; discriminate
    end.
Definition eq := @eq string.
Hint Resolve string_compare_eq_refl.
Lemma eq_Eq : forall x y, x = y -> string_compare x y = Eq.
(* hint proof tokens: 14 *)
Proof.
    intros; subst; auto.
  Qed.
Lemma nat_of_ascii_injective :
    forall a b, nat_of_ascii a = nat_of_ascii b <-> a = b.
(* hint proof tokens: 54 *)
Proof.
    intros a b; split; intro H;
    [ apply (f_equal ascii_of_nat) in H;
      repeat rewrite ascii_nat_embedding in H
    | apply (f_equal nat_of_ascii) in H ]; trivial.
  Qed.
Lemma Eq_eq : forall x y, string_compare x y = Eq -> x = y.
(* hint proof tokens: 61 *)
Proof.
    induction x;
      destruct y;
      simpl;
      first [ discriminate
            | intros;
              f_equal;
              destruct_comparisons;
              autorewrite_nat_compare;
              rewrite nat_of_ascii_injective in *
            | idtac ];
      intuition.
  Qed.
Lemma Eq_eq_iff : forall x y, x = y <-> string_compare x y = Eq.
Proof.
(* original proof tokens: 22 *)
(* generated proof tokens: 27 *)

split; [intros; apply eq_Eq; assumption | intros; apply Eq_eq; assumption].
Qed.

Definition eq_refl := @eq_refl string.
Definition eq_sym := @eq_sym string.
Definition eq_trans := @eq_trans string.
Definition lt x y :=
    string_compare x y = Lt.
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
(* original proof tokens: 73 *)
intros x y z Hxy Hyz.
induction x;
  intros; simpl in *;
  try discriminate;
  intros; simpl in *;
  try discriminate;
  intros; simpl in *;
  try discriminate.
destruct y; simpl in *; try discriminate.
destruct z; simpl in *; try discriminate.
destruct (Nat.compare (nat_of_ascii a) (nat_of_ascii a0)) eqn :?.
destruct Heqc; try discriminate.
(* No more tactics to try *)
Admitted.

Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y.
(* hint proof tokens: 35 *)
Proof.
    unfold lt, not in *;
    intros;
    rewrite Eq_eq_iff in *;
    exfalso_from_equalities.
  Qed.
Lemma Lt_Gt : forall x y, string_compare x y = Gt <-> string_compare y x = Lt.
Proof.
(* original proof tokens: 120 *)

(* No more tactics to try *)
Admitted.

Definition compare x y : OrderedType.Compare lt eq x y.
Proof.
    destruct (string_compare x y) eqn:comp;
      unfold lt;
      [ constructor 2; apply Eq_eq
      | constructor 1
      | constructor 3; apply Lt_Gt];
      trivial.
  Qed.
Definition eq_dec : forall (x y: string), { x = y } + { x <> y }.
Proof.
    exact string_dec.
  Qed.
End String_as_OT.
