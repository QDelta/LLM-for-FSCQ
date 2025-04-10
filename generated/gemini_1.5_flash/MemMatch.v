Require Import Mem.
Require Import List Lia Ring Word Pred Prog Hoare SepAuto BasicProg Array.
Require Import FunctionalExtensionality.
Set Implicit Arguments.
Set Default Proof Using "Type".
Section COND_BIJECTION.
Variables A B : Type.
Variable f : A -> B.
Variable PA : A -> Prop.
Variable PB : B -> Prop.
Definition cond_injective :=
    forall x y : A, PA x -> PA y -> f x = f y -> x = y.
Definition cond_surjective :=
    forall y : B, PB y -> {x : A | PA x /\ f x = y}.
Inductive cond_bijective : Prop :=
    CondBijective : cond_injective -> cond_surjective -> cond_bijective.
Section BIJECTION_INVERSION.
Variable f' : B -> A.
Definition cond_left_inverse := 
      forall x : A, PA x -> PB (f x) /\ f' (f x) = x.
Definition cond_right_inverse := 
      forall y : B, PB y -> PA (f' y) /\ f (f' y) = y.
Definition cond_inverse := 
      cond_left_inverse /\ cond_right_inverse.
Lemma cond_left_inv_inj : cond_left_inverse -> cond_injective.
Proof.
(* original proof tokens: 53 *)
(* generated proof tokens: 86 *)

intros H x y HPAx HPAy Hfxy.
eapply H in HPAx.
destruct HPAx as [HPAx Hf'x].
eapply H in HPAy.
destruct HPAy as [HPAy Hf'y].
rewrite Hfxy in Hf'x.
rewrite Hf'x in Hf'y.
assumption.
Qed.

Lemma cond_right_inv_surj : cond_right_inverse -> cond_surjective.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma cond_inv2bij : cond_inverse -> cond_bijective.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Lemma cond_inv_rewrite_right : forall y,
      cond_inverse -> PB y -> f (f' y) = y.
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Lemma cond_inv_rewrite_left : forall x,
      cond_inverse -> PA x -> f' (f x) = x.
Proof.
(* original proof tokens: 15 *)
(* generated proof tokens: 27 *)

intros.
destruct H as [H1 H2].
eapply H1; eauto.
Qed.

Lemma cond_inv_domain_right : forall y,
      cond_inverse -> PB y -> PA (f' y).
Proof.
(* original proof tokens: 15 *)
(* generated proof tokens: 33 *)

intros y Hinv Hy.
destruct Hinv as [Hlinv Hrinv].
apply Hrinv.
auto.
Qed.

Lemma cond_inv_domain_left : forall x,
      cond_inverse -> PA x -> PB (f x).
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

End BIJECTION_INVERSION.
End COND_BIJECTION.
Theorem cond_inverse_sym : forall A B PA PB (f : A -> B) (f' : B -> A),
  cond_inverse f PA PB f'
  -> cond_inverse f' PB PA f.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Theorem cond_inv2bij_inv : forall A B PA PB (f : A -> B) (f' : B -> A),
  cond_inverse f PA PB f'
  -> cond_bijective f' PB PA.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Section MEMMATCH.
Variable AT1 : Type.
Variable AT2 : Type.
Variable atrans : AT1 -> AT2.
Variable AEQ1 : EqDec AT1.
Variable AEQ2 : EqDec AT2.
Variable V : Type.
Variable m1 : @mem AT1 AEQ1 V.
Variable m2 : @mem AT2 AEQ2 V.
Variable AP1 : AT1 -> Prop.
Variable AP2 : AT2 -> Prop.
Variable AP1_dec : forall a1, AP1 a1 \/ ~ AP1 a1.
Variable AP2_dec : forall a2, AP2 a2 \/ ~ AP2 a2.
Variable AP1_ok : forall a1, indomain a1 m1 -> AP1 a1.
Variable AP2_ok : forall a2, indomain a2 m2 -> AP2 a2.
Definition mem_atrans AT1 AEQ1 V AT2 AEQ2
    f (m : @mem AT1 AEQ1 V) (m' : @mem AT2 AEQ2 V) (P : AT1 -> Prop) :=
    forall a, P a -> m a = m' (f a).
Variable MTrans : mem_atrans atrans m1 m2 AP1.
Lemma mem_atrans_indomain : forall a1 x,
    indomain a1 m1 ->
    m1 a1 = x -> m2 (atrans a1) = x.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma mem_atrans_mem_except : forall a (ap : AP1 a),
    cond_bijective atrans AP1 AP2 ->
    mem_atrans atrans (mem_except m1 a) (mem_except m2 (atrans a)) AP1.
Proof.
(* original proof tokens: 82 *)
intros.
unfold mem_atrans.
(* No more tactics to try *)
Admitted.

Section MEMMATCH_INVERSION.
Variable ainv : AT2 -> AT1.
Variable HInv : cond_inverse atrans AP1 AP2 ainv.
Lemma mem_ainv_any : forall a (ap : AP2 a) x,
      m1 (ainv a) = x -> m2 a = x.
Proof.
(* original proof tokens: 67 *)
intros a HAp2 x Hx.
(* No more tactics to try *)
Admitted.

Lemma mem_atrans_inv_ptsto : forall a (ap : AP2 a) F v,
      (F * (ainv a) |-> v)%pred m1
      -> (any * a |-> v)%pred m2.
Proof.
(* original proof tokens: 45 *)
intros.
unfold sep_star.
(* No more tactics to try *)
Admitted.

Lemma mem_atrans_inv_notindomain : forall a (ap : AP2 a),
      notindomain (ainv a) m1 -> notindomain a m2.
Proof.
(* original proof tokens: 32 *)
intros a HAp2 Hnot.
apply notindomain_not_indomain; unfold notindomain; intro Hindomain.
apply notindomain_not_indomain in Hnot; auto.
apply HInv in HAp2; destruct HInv as [Hleft Hright]; destruct HAp2 as [? HAp2'].
apply AP2_ok in Hindomain; auto.
apply Hnot; auto.
apply Hleft in H; auto.
apply HInv in Hindomain; auto.
apply notindomain_not_indomain in Hnot; auto.
(* No more tactics to try *)
Admitted.

Lemma mem_atrans_inv_indomain : forall a (ap : AP2 a),
      indomain (ainv a) m1 -> indomain a m2.
Proof.
(* original proof tokens: 38 *)
intros a HAp2 Hindomain.
(* No more tactics to try *)
Admitted.

Lemma mem_atrans_emp :
      emp m1 -> emp m2.
Proof.
(* original proof tokens: 112 *)
intros H.
(* No more tactics to try *)
Admitted.

Lemma mem_ainv_mem_except : forall a (ap : AP2 a),
      mem_atrans atrans (mem_except m1 (ainv a)) (mem_except m2 a) AP1.
Proof.
(* original proof tokens: 102 *)
intros a HAp2.
unfold mem_atrans.
(* No more tactics to try *)
Admitted.

Lemma mem_ainv_mem_upd : forall a v (ap : AP2 a),
      mem_atrans atrans (Mem.upd m1 (ainv a) v) (Mem.upd m2 a v) AP1.
Proof.
(* original proof tokens: 87 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma mem_atrans_cond_inv : mem_atrans ainv m2 m1 AP2.
Proof.
(* original proof tokens: 64 *)

(* No more tactics to try *)
Admitted.

End MEMMATCH_INVERSION.
End MEMMATCH.
