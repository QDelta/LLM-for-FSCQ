Require Import Arith.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import Mem.
Require Import RelationClasses.
Require Import Morphisms.
Require Import List.
Set Implicit Arguments.
Section GenPredDef.
Variable AT : Type.
Variable AEQ : EqDec AT.
Variable V : Type.
Definition pred := @mem AT AEQ V -> Prop.
Definition ptsto (a : AT) (v : V) : pred :=
  fun m => m a = Some v /\ forall a', a <> a' -> m a' = None.
Definition impl (p q : pred) : pred :=
  fun m => p m -> q m.
Definition and (p q : pred) : pred :=
  fun m => p m /\ q m.
Definition or (p q : pred) : pred :=
  fun m => p m \/ q m.
Definition foral_ A (p : A -> pred) : pred :=
  fun m => forall x, p x m.
Definition exis A (p : A -> pred) : pred :=
  fun m => exists x, p x m.
Definition uniqpred A (p : A -> pred) (x : A) : pred :=
  fun m => p x m /\ (forall (x' : A), p x' m -> x = x').
Definition emp : pred :=
  fun m => forall a, m a = None.
Definition any : pred :=
  fun m => True.
Definition lift (P : Prop) : pred :=
  fun m => P.
Definition lift_empty (P : Prop) : pred :=
  fun m => P /\ forall a, m a = None.
Definition pimpl (p q : pred) := forall m, p m -> q m.
Definition piff (p q : pred) : Prop := (pimpl p q) /\ (pimpl q p).
Definition mem_disjoint (m1 m2 : @mem AT AEQ V) :=
  ~ exists a (v1 v2 : V), m1 a = Some v1 /\ m2 a = Some v2.
Definition mem_union (m1 m2 : @mem AT AEQ V) : (@mem AT AEQ V) := fun a =>
  match m1 a with
  | Some v => Some v
  | None => m2 a
  end.
Definition sep_star_impl (p1: pred) (p2: pred) : pred :=
  fun m => exists m1 m2, m = mem_union m1 m2 /\ mem_disjoint m1 m2 /\ p1 m1 /\ p2 m2.
Definition septract (p q : pred) : pred :=
  fun m => exists m1, mem_disjoint m m1 /\ p m1 /\ q (mem_union m m1).
Definition indomain (a: AT) (m: @mem AT AEQ V) :=
  exists (v:V), m a = Some v.
Definition notindomain (a : AT) (m : @mem AT AEQ V) :=
  m a = None.
Definition diskIs (m : @mem AT AEQ V) : pred :=
  fun m' => m = m'.
Definition mem_except (m: @mem AT AEQ V) (a: AT) : @mem AT AEQ V :=
  fun a' => if AEQ a' a then None else m a'.
Definition pred_apply (m : @mem AT AEQ V) (p : pred) := p m.
Definition strictly_exact (p : pred) : Prop :=
  forall m1 m2, p m1 -> p m2 -> m1 = m2.
Definition exact_domain (p : pred) : Prop :=
  forall m1 m2, p m1 -> p m2 -> (forall a, m1 a = None <-> m2 a = None).
Definition precise (p : pred) : Prop :=
  forall m1 m1' m2 m2',
  mem_union m1 m1' = mem_union m2 m2' ->
  mem_disjoint m1 m1' ->
  mem_disjoint m2 m2' ->
  p m1 -> p m2 -> m1 = m2.
End GenPredDef.
Arguments pred {AT AEQ V}.
Arguments emp {AT AEQ V} _.
Arguments any {AT AEQ V} _.
Arguments pimpl {AT AEQ V} _ _.
Arguments piff {AT AEQ V} _ _.
Arguments sep_star_impl {AT AEQ V} _ _ _.
Arguments septract {AT AEQ V} _ _ _.
Arguments indomain {AT AEQ V} _ _.
Arguments notindomain {AT AEQ V} _ _.
Arguments diskIs {AT AEQ V} _ _.
Arguments pred_apply {AT AEQ V} _ _.
Arguments strictly_exact {AT AEQ V} _.
Arguments exact_domain {AT AEQ V} _.
Arguments precise {AT AEQ V} _.
Hint Unfold pimpl.
Hint Unfold piff.
Infix "|->" := ptsto (at level 35) : pred_scope.
Bind Scope pred_scope with pred.
Delimit Scope pred_scope with pred.
Infix "-p->" := impl (right associativity, at level 95) : pred_scope.
Infix "/\" := and : pred_scope.
Infix "\/" := or : pred_scope.
Notation "'foral' x .. y , p" := (foral_ (fun x => .. (foral_ (fun y => p)) ..)) (at level 200, x binder, right associativity) : pred_scope.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : pred_scope.
Notation "a |->?" := (exists v, a |-> v)%pred (at level 35) : pred_scope.
Notation "'exists' ! x .. y , p" := (exis (uniqpred (fun x => .. (exis (uniqpred (fun y => p))) ..))) : pred_scope.
Notation "[ P ]" := (lift P) : pred_scope.
Notation "[[ P ]]" := (lift_empty P) : pred_scope.
Notation "p =p=> q" := (pimpl p%pred q%pred) (right associativity, at level 90).
Notation "p <=p=> q" := (piff p%pred q%pred) (at level 90).
Notation "m ## p" := (pred_apply m p%pred) (at level 90).
Theorem exists_unique_incl_exists : forall A P,
  (exists ! (x:A), P x) -> exists (x:A), P x.
(* hint proof tokens: 21 *)
Proof.
  intros.
  inversion H.
  inversion H0.
  eauto.
Qed.
Module Type SEP_STAR.
Parameter sep_star : forall {AT:Type} {AEQ:EqDec AT} {V:Type}, @pred AT AEQ V -> @pred AT AEQ V -> @pred AT AEQ V.
Axiom sep_star_is : @sep_star = @sep_star_impl.
End SEP_STAR.
Module Sep_Star : SEP_STAR.
Definition sep_star := @sep_star_impl.
Theorem sep_star_is : @sep_star = @sep_star_impl.
Proof.
(* original proof tokens: 8 *)
(* generated proof tokens: 14 *)

Proof. 
  reflexivity. 
Qed.

End Sep_Star.
Definition sep_star := @Sep_Star.sep_star.
Definition sep_star_is := Sep_Star.sep_star_is.
Arguments sep_star {AT AEQ V} _ _ _.
Infix "*" := sep_star : pred_scope.
Notation "p --* q" := (septract p%pred q%pred) (at level 40) : pred_scope.
Notation "⟦⟦ P ⟧⟧" := (lift_empty P) : pred_scope.
Notation "p '⇨⇨' q" := (pimpl p%pred q%pred) (right associativity, at level 90).
Notation "p '⇦⇨' q" := (piff p%pred q%pred) (at level 90).
Infix "✶" := sep_star (at level 80) : pred_scope.
Infix "⋀" := and (at level 80) : pred_scope.
Infix "⋁" := or (at level 85) : pred_scope.
Ltac safedeex :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]
  end.
Ltac deex :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]; intuition subst
  end.
Ltac deex_unique :=
  match goal with
  | [ H : exists ! (varname : _), _ |- _] =>
    let newvar := fresh varname in
    let Hunique := fresh in
    let Huniqueness := fresh "H" newvar "_uniq" in
    destruct H as [newvar Hunique];
    inversion Hunique as [? Huniqueness]; clear Hunique;
    intuition subst
  end.
Ltac pred_unfold :=
  unfold impl, and, or, foral_, exis, uniqpred, lift in *.
Ltac pred := pred_unfold;
  repeat (repeat deex; simpl in *;
    intuition (try (congruence || lia);
      try autorewrite with core in *; eauto); try subst).
Ltac unfold_sep_star :=
  unfold sep_star; rewrite sep_star_is; unfold sep_star_impl.
Section GenPredThm.
Set Default Proof Using "Type".
Variable AT : Type.
Variable AEQ : EqDec AT.
Variable V : Type.
Theorem pimpl_refl : forall (p : @pred AT AEQ V), p =p=> p.
(* hint proof tokens: 8 *)
Proof.
  pred.
Qed.
Hint Resolve pimpl_refl.
Theorem mem_disjoint_comm:
  forall (m1 m2 : @mem AT AEQ V),
  mem_disjoint m1 m2 <-> mem_disjoint m2 m1.
Proof.
(* original proof tokens: 26 *)
intros m1 m2. split; intros H.
(* No more tactics to try *)
Admitted.

Theorem mem_disjoint_assoc_1:
  forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint m1 m2 ->
  mem_disjoint (mem_union m1 m2) m3 ->
  mem_disjoint m1 (mem_union m2 m3).
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Theorem mem_disjoint_assoc_2:
  forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint m2 m3 ->
  mem_disjoint m1 (mem_union m2 m3) ->
  mem_disjoint (mem_union m1 m2) m3.
Proof.
(* original proof tokens: 81 *)
unfold mem_disjoint in *; unfold mem_union in *; intros.
firstorder.
apply mem_disjoint_comm.
unfold mem_disjoint. intros.
(* No more tactics to try *)
Admitted.

Theorem mem_disjoint_union:
  forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint (mem_union m1 m2) m3 ->
  mem_disjoint m2 m3.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Theorem mem_disjoint_union_2:
  forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint m1 (mem_union m2 m3) ->
  mem_disjoint m1 m2.
Proof.
(* original proof tokens: 47 *)
unfold mem_disjoint in *; intros.
intro H1.
apply H.
deex.
deex.
(* No more tactics to try *)
Admitted.

Theorem mem_disjoint_upd:
  forall (m1 m2 : @mem AT AEQ V) a v v0,
  m1 a = Some v0 ->
  mem_disjoint m1 m2 ->
  mem_disjoint (upd m1 a v) m2.
Proof.
(* original proof tokens: 37 *)
intros m1 m2 a v v0 H H0.
(* No more tactics to try *)
Admitted.

Lemma mem_disjoint_either:
  forall (m1 m2 : @mem AT AEQ V) a v,
  mem_disjoint m1 m2
  -> m1 a = Some v -> m2 a = None.
(* hint proof tokens: 58 *)
Proof.
  unfold mem_disjoint; intros; firstorder.
  pose proof (H a); firstorder.
  pose proof (H1 v); firstorder.
  destruct (m2 a); auto.
  pose proof (H2 v0); firstorder.
Qed.
Lemma mem_disjoint_insert_l : forall (m1 m2 : @mem AT AEQ V) a v,
  mem_disjoint m1 m2 ->
  m2 a = None ->
  mem_disjoint (insert m1 a v) m2.
(* hint proof tokens: 68 *)
Proof.
  unfold insert, mem_disjoint; intros.
  contradict H; repeat deex.
  destruct (AEQ a0 a) in H1; subst; try congruence.
  destruct (m1 a) eqn:?;
  exists a0; do 2 eexists; eauto.
Qed.
Theorem mem_union_comm:
  forall (m1 m2 : @mem AT AEQ V),
  mem_disjoint m1 m2 ->
  mem_union m1 m2 = mem_union m2 m1.
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Theorem mem_disjoint_union_cancel:
  forall (m1 m2 m2' : @mem AT AEQ V),
  mem_disjoint m1 m2 ->
  mem_disjoint m1 m2' ->
  mem_union m1 m2 = mem_union m1 m2' ->
  m2 = m2'.
Proof.
(* original proof tokens: 171 *)

(* No more tactics to try *)
Admitted.

Theorem mem_union_addr:
  forall (m1 m2 : @mem AT AEQ V) a v,
  mem_disjoint m1 m2 ->
  m1 a = Some v ->
  mem_union m1 m2 a = Some v.
(* hint proof tokens: 22 *)
Proof.
  unfold mem_disjoint, mem_union; intros; rewrite H0; auto.
Qed.
Theorem mem_union_upd:
  forall (m1 m2 : @mem AT AEQ V) a v,
  mem_union (upd m1 a v) m2 = upd (mem_union m1 m2) a v.
Proof.
(* original proof tokens: 33 *)
unfold mem_union, upd.
unfold mem_union; intros; extensionality a0.
transitivity (if AEQ a0 a then Some v else match m1 a0 with | Some v => Some v | None => m2 a0 end).
(* No more tactics to try *)
Admitted.

Theorem mem_union_assoc:
  forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint m1 m2 ->
  mem_disjoint (mem_union m1 m2) m3 ->
  mem_union (mem_union m1 m2) m3 = mem_union m1 (mem_union m2 m3).
Proof.
(* original proof tokens: 33 *)
(* generated proof tokens: 89 *)
unfold mem_union; intros. 
apply functional_extensionality; intro a. 
destruct (m1 a) eqn:H1; destruct (m2 a) eqn:H2; destruct (m3 a) eqn:H3; simpl.
congruence.
congruence.
congruence.
congruence.
congruence.
congruence.
firstorder.
reflexivity.
Qed.

Lemma mem_union_sel_none : forall (m1 m2 : @mem AT AEQ V) a,
  m1 a = None ->
  m2 a = None ->
  mem_union m1 m2 a = None.
(* hint proof tokens: 23 *)
Proof.
  intros.
  unfold mem_union.
  destruct (m1 a); eauto.
Qed.
Lemma mem_union_none_sel : forall (m1 m2 : @mem AT AEQ V) a,
  mem_union m1 m2 a = None ->
  m1 a = None /\  m2 a = None.
(* hint proof tokens: 40 *)
Proof.
  unfold mem_union; intros.
  destruct (m1 a) eqn:?; destruct (m2 a) eqn:?; intuition.
  congruence.
Qed.
Lemma mem_union_sel_l : forall (m1 m2 : @mem AT AEQ V) a,
  mem_disjoint m1 m2 ->
  m2 a = None ->
  mem_union m1 m2 a = m1 a.
(* hint proof tokens: 23 *)
Proof.
  intros.
  unfold mem_union.
  destruct (m1 a); eauto.
Qed.
Lemma mem_union_sel_r : forall (m1 m2 : @mem AT AEQ V) a,
  mem_disjoint m1 m2 ->
  m1 a = None ->
  mem_union m1 m2 a = m2 a.
(* hint proof tokens: 28 *)
Proof.
  intros.
  unfold mem_union.
  destruct (m1 a); eauto.
  congruence.
Qed.
Lemma mem_union_insert_comm : forall (m1 m2 : @mem AT AEQ V) a v,
  m1 a = None ->
  m2 a = None ->
  insert (mem_union m1 m2) a v = mem_union (insert m1 a v) m2.
Proof.
(* original proof tokens: 53 *)
unfold insert, mem_union; intros. 
destruct (m1 a) eqn:?; destruct (m2 a) eqn:?; auto.
apply functional_extensionality; intro a'.
rewrite H in Heqo.
(* No more tactics to try *)
Admitted.

Lemma mem_disjoint_mem_union_split_l : forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint m1 m3 ->
  mem_disjoint m2 m3 ->
  mem_disjoint (mem_union m1 m2) m3.
(* hint proof tokens: 68 *)
Proof.
  unfold mem_disjoint, mem_union; intuition repeat deex.
  destruct (m1 a) eqn:?.
  - inversion H2; subst.
    apply H; do 3 eexists; intuition eauto.
  - apply H0; do 3 eexists; intuition eauto.
Qed.
Lemma mem_disjoint_mem_union_split_r : forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint m1 m2 ->
  mem_disjoint m1 m3 ->
  mem_disjoint m1 (mem_union m2 m3).
Proof.
(* original proof tokens: 43 *)
(* generated proof tokens: 74 *)
unfold mem_disjoint, mem_union; intros. 
intuition repeat deex. 
destruct (m2 a) eqn:?; destruct (m3 a) eqn:?; intuition eauto.
apply H0; eauto.
firstorder.
apply H0.
eauto.
inversion H2.
congruence.
Qed.

Theorem sep_star_comm1:
  forall (p1 p2 : @pred AT AEQ V),
  (p1 * p2 =p=> p2 * p1)%pred.
(* hint proof tokens: 41 *)
Proof.
  unfold pimpl; unfold_sep_star; pred.
  exists m2; exists m1. intuition eauto using mem_union_comm. apply mem_disjoint_comm; auto.
Qed.
Theorem sep_star_comm:
  forall (p1 p2 : @pred AT AEQ V),
  (p1 * p2 <=p=> p2 * p1)%pred.
(* hint proof tokens: 17 *)
Proof.
  unfold piff; split; apply sep_star_comm1.
Qed.
Theorem sep_star_assoc_1:
  forall (p1 p2 p3 : @pred AT AEQ V),
  (p1 * p2 * p3 =p=> p1 * (p2 * p3))%pred.
(* hint proof tokens: 73 *)
Proof.
  unfold pimpl; unfold_sep_star; pred.
  eexists; eexists (mem_union _ _); intuition eauto.
  apply mem_union_assoc; auto.
  apply mem_disjoint_assoc_1; auto.
  eexists; eexists; intuition eauto.
  eapply mem_disjoint_union; eauto.
Qed.
Theorem sep_star_assoc_2:
  forall (p1 p2 p3 : @pred AT AEQ V),
  (p1 * (p2 * p3) =p=> p1 * p2 * p3)%pred.
Proof.
(* original proof tokens: 150 *)
unfold piff, sep_star; pred.
(* No more tactics to try *)
Admitted.

Theorem sep_star_assoc:
  forall (p1 p2 p3 : @pred AT AEQ V),
  (p1 * p2 * p3 <=p=> p1 * (p2 * p3))%pred.
Proof.
(* original proof tokens: 24 *)
(* generated proof tokens: 27 *)

unfold piff; split; [apply sep_star_assoc_1 | apply sep_star_assoc_2].
Qed.

Theorem sep_star_mem_union :
  forall (p q : @pred AT AEQ V) mp mq,
  mem_disjoint mp mq ->
  p mp -> q mq ->
  (p * q)%pred (mem_union mp mq).
(* hint proof tokens: 21 *)
Proof.
  unfold_sep_star; intros.
  do 2 eexists; intuition.
Qed.
Local Hint Extern 1 =>
  match goal with
    | [ |- upd _ ?a ?v ?a = Some ?v ] => apply upd_eq; auto
  end.
Lemma pimpl_exists_l:
  forall T p (q : @pred AT AEQ V),
  (forall x:T, p x =p=> q) ->
  (exists x:T, p x) =p=> q.
Proof.
(* original proof tokens: 9 *)
apply pimpl_refl.
(* No more tactics to try *)
Admitted.

Lemma pimpl_exists_r:
  forall T (p : @pred AT AEQ V) q,
  (exists x:T, p =p=> q x) ->
  (p =p=> exists x:T, q x).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_exists_l_star:
  forall T p (q : @pred AT AEQ V) r,
  ((exists x:T, p x * r) =p=> q) ->
  (exists x:T, p x) * r =p=> q.
(* hint proof tokens: 41 *)
Proof.
  unfold pimpl, exis; unfold_sep_star; intros.
  repeat deex.
  eapply H.
  do 3 eexists.
  intuition eauto.
Qed.
Lemma pimpl_exists_r_star:
  forall T p (q : @pred AT AEQ V),
  (exists x:T, p x * q) =p=> ((exists x:T, p x) * q).
Proof.
(* original proof tokens: 36 *)
repeat unfold_sep_star; pred.
apply pimpl_exists_l.
unfold pimpl. pred.
(* No more tactics to try *)
Admitted.

Lemma pimpl_exists_r_star_r:
  forall T (p : T -> pred) (q : @pred AT AEQ V),
  (exists x : T, p x) * q =p=>  (exists x : T, p x * q).
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_exists_l_star_r:
  forall T (p : T -> pred) (q : @pred AT AEQ V),
  q * (exists x : T, p x) =p=>  (exists x : T, q * p x).
Proof.
(* original proof tokens: 36 *)
unfold piff. unfold_sep_star. pred. intuition.
unfold pimpl. pred. eauto.
(* No more tactics to try *)
Admitted.

Lemma pimpl_exists_and_l:
  forall T p (r : @pred AT AEQ V),
  (exists x:T, p x /\ r) =p=> ((exists x:T, p x) /\ r).
Proof.
(* original proof tokens: 9 *)
pred.
apply pimpl_exists_l.
(* No more tactics to try *)
Admitted.

Lemma pimpl_exists_and_r:
  forall T p (r : @pred AT AEQ V),
  (exists x:T, r /\ p x) =p=> (r /\ (exists x:T, p x)).
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 23 *)

unfold pimpl, exis, and; intros; pred; deex.
Qed.

Lemma pimpl_and_l_exists:
  forall T p (r : @pred AT AEQ V),
  ((exists x:T, p x) /\ r) =p=> (exists x:T, p x /\ r).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma pimpl_and_r_exists:
  forall T p (r : @pred AT AEQ V),
  (r /\ (exists x:T, p x)) =p=> (exists x:T, r /\ p x).
Proof.
(* original proof tokens: 9 *)
pred.
(* No more tactics to try *)
Admitted.

Lemma pimpl_l_and : forall (p q : @pred AT AEQ V),
  p /\ q =p=> p.
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma pimpl_r_and : forall (p q : @pred AT AEQ V),
  p /\ q =p=> q.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_and_dup : forall (p : @pred AT AEQ V),
  p <=p=> p /\ p.
Proof.
(* original proof tokens: 9 *)
pred.
apply pimpl_refl.
(* No more tactics to try *)
Admitted.

Lemma pimpl_trans:
  forall (a b c : @pred AT AEQ V),
  (a =p=> b) ->
  (b =p=> c) ->
  (a =p=> c).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_trans2:
  forall (a b c : @pred AT AEQ V),
  (b =p=> c) ->
  (a =p=> b) ->
  (a =p=> c).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma piff_trans:
  forall (a b c : @pred AT AEQ V),
  (a <=p=> b) ->
  (b <=p=> c) ->
  (a <=p=> c).
(* hint proof tokens: 20 *)
Proof.
  unfold piff; intuition; eapply pimpl_trans; eauto.
Qed.
Lemma piff_comm:
  forall (a b : @pred AT AEQ V),
  (a <=p=> b) ->
  (b <=p=> a).
(* hint proof tokens: 11 *)
Proof.
  unfold piff; intuition.
Qed.
Lemma piff_refl:
  forall (a : @pred AT AEQ V),
  (a <=p=> a).
Proof.
(* original proof tokens: 11 *)
(* generated proof tokens: 8 *)

pred.
Qed.

Lemma pimpl_apply:
  forall (p q:@pred AT AEQ V) m,
  (p =p=> q) ->
  p m ->
  q m.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma piff_apply:
  forall (p q:@pred AT AEQ V) m,
  (p <=p=> q) ->
  q m ->
  p m.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_fun_l:
  forall (p:@pred AT AEQ V),
  (fun m => p m) =p=> p.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_fun_r:
  forall (p:@pred AT AEQ V),
  p =p=> (fun m => p m).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma pimpl_sep_star:
  forall (a b c d : @pred AT AEQ V),
  (a =p=> c) ->
  (b =p=> d) ->
  (a * b =p=> c * d).
(* hint proof tokens: 35 *)
Proof.
  unfold pimpl; unfold_sep_star; intros.
  do 2 deex.
  do 2 eexists.
  intuition eauto.
Qed.
Lemma pimpl_and:
  forall (a b c d : @pred AT AEQ V),
  (a =p=> c) ->
  (b =p=> d) ->
  (a /\ b =p=> c /\ d).
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 16 *)

unfold pimpl; unfold and; pred.
Qed.

Lemma pimpl_or : forall (p q p' q' : @pred AT AEQ V),
  p =p=> p'
  -> q =p=> q'
  -> p \/ q =p=> p' \/ q'.
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma pimpl_ext : forall (p q p' q' : @pred AT AEQ V),
  p  =p=> q  ->
  p' =p=> p  ->
  q  =p=> q' ->
  p' =p=> q'.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma sep_star_lift_l:
  forall (a: Prop) (b c: @pred AT AEQ V),
  (a -> (b =p=> c)) ->
  b * [[a]] =p=> c.
(* hint proof tokens: 67 *)
Proof.
  unfold pimpl, lift_empty; unfold_sep_star; intros.
  repeat deex.
  assert (mem_union m1 m2 = m1).
  apply functional_extensionality; unfold mem_union; intros.
  case_eq (m1 x); pred.
  rewrite H. eauto.
Qed.
Lemma sep_star_lift_r':
  forall (b: Prop) (a c: @pred AT AEQ V),
  (a =p=> [b] /\ c) ->
  (a =p=> [[b]] * c).
Proof.
(* original proof tokens: 54 *)
unfold pimpl, lift_empty; unfold_sep_star; intros.
repeat deex.
eexists; eexists. intuition.
(* No more tactics to try *)
Admitted.

Lemma sep_star_lift_r:
  forall (a b: @pred AT AEQ V) (c: Prop),
  (a =p=> b /\ [c]) ->
  (a =p=> b * [[c]]).
(* hint proof tokens: 34 *)
Proof.
  intros.
  eapply pimpl_trans; [|apply sep_star_comm].
  apply sep_star_lift_r'.
  firstorder.
Qed.
Theorem sep_star_lift_apply : forall (a : Prop) (b : @pred AT AEQ V) (m : mem),
  (b * [[a]])%pred m -> (b m /\ a).
Proof.
(* original proof tokens: 62 *)

(* No more tactics to try *)
Admitted.

Theorem sep_star_lift_apply' : forall (a : Prop) (b : @pred AT AEQ V) (m : mem),
  b m -> a -> (b * [[ a ]])%pred m.
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_star_emp: forall (p : @pred AT AEQ V), p =p=> emp * p.
Proof.
(* original proof tokens: 40 *)
apply pimpl_refl.
(* No more tactics to try *)
Admitted.

Lemma star_emp_pimpl: forall (p : @pred AT AEQ V), emp * p =p=> p.
(* hint proof tokens: 72 *)
Proof.
  unfold pimpl; unfold_sep_star; intros.
  unfold emp in *; pred.
  assert (mem_union m1 m2 = m2).
  apply functional_extensionality; unfold mem_union; intros.
  case_eq (m1 x); intuition. rewrite H1 in H0; pred.
  pred.
Qed.
Lemma emp_star: forall p, p <=p=> (@emp AT AEQ V) * p.
Proof.
(* original proof tokens: 24 *)
unfold piff. unfold emp. unfold sep_star. pred.
(* No more tactics to try *)
Admitted.

Lemma emp_star_r: forall (F:@pred AT AEQ V),
  F =p=> (F * emp)%pred.
(* hint proof tokens: 29 *)
Proof.
  intros.
  eapply pimpl_trans.
  2: apply sep_star_comm.
  apply emp_star.
Qed.
Lemma piff_star_r: forall (a b c : @pred AT AEQ V),
  (a <=p=> b) ->
  (a * c <=p=> b * c).
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Lemma piff_star_l: forall (a b c : @pred AT AEQ V),
  (a <=p=> b) ->
  (c * a <=p=> c * b).
(* hint proof tokens: 30 *)
Proof.
  unfold piff, pimpl; unfold_sep_star; intuition;
    repeat deex; repeat eexists; eauto.
Qed.
Lemma piff_l :
  forall (p p' q : @pred AT AEQ V),
  (p <=p=> p')
  -> (p' =p=> q)
  -> (p =p=> q).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma piff_r :
  forall (p q q' : @pred AT AEQ V),
  (q <=p=> q')
  -> (p =p=> q')
  -> (p =p=> q).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma sep_star_lift2and:
  forall (a : @pred AT AEQ V) b,
  (a * [[b]]) =p=> a /\ [b].
Proof.
(* original proof tokens: 69 *)
(* generated proof tokens: 51 *)
unfold pimpl, sep_star, lift_empty, and; intros. pred.
apply sep_star_lift_apply in H.
apply (proj1 H).
apply sep_star_lift_apply in H.
apply (proj2 H).
Qed.

Lemma sep_star_and2lift:
  forall (a : @pred AT AEQ V) b,
  (a /\ [b]) =p=> (a * [[b]]).
(* hint proof tokens: 84 *)
Proof.
  unfold and, lift, lift_empty, pimpl; unfold_sep_star.
  intros; repeat deex.
  do 2 eexists; intuition; eauto.
  - unfold mem_union.
    apply functional_extensionality.
    intros; destruct (m x); auto.
  - unfold mem_disjoint, not; intros.
    repeat deex.
    congruence.
Qed.
Lemma ptsto_exact_domain : forall a v,
  exact_domain (@ptsto AT AEQ V a v).
(* hint proof tokens: 49 *)
Proof.
  unfold exact_domain, ptsto; intuition.
  destruct (AEQ a a0); subst; intuition; congruence.
  destruct (AEQ a a0); subst; intuition; congruence.
Qed.
Lemma ptsto_exis_exact_domain : forall a,
  @exact_domain AT AEQ V (a |->?).
Proof.
(* original proof tokens: 91 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_mem_is : forall a v,
  @ptsto AT AEQ V a v (fun x => if (AEQ x a) then Some v else None).
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_exis_mem_is : forall a v,
  (exists v, @ptsto AT AEQ V a v)%pred (fun x => if (AEQ x a) then Some v else None).
Proof.
(* original proof tokens: 48 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_valid:
  forall a v F (m : @mem AT AEQ V),
  (a |-> v * F)%pred m
  -> m a = Some v.
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_valid':
  forall a v F (m : @mem AT AEQ V),
  (F * (a |-> v))%pred m
  -> m a = Some v.
(* hint proof tokens: 49 *)
Proof.
  unfold ptsto; unfold_sep_star.
  intros; repeat deex.
  rewrite mem_union_comm; eauto.
  apply mem_union_addr; eauto.
  rewrite mem_disjoint_comm; eauto.
Qed.
Lemma ptsto_ne : forall (m : @mem AT AEQ V) a a' v,
  (a |-> v)%pred m ->
  a <> a' ->
  m a' = None.
(* hint proof tokens: 12 *)
Proof.
  unfold ptsto; intuition.
Qed.
Lemma ptsto_upd_disjoint: forall V (F : @pred AT AEQ V) a v m,
  F m -> m a = None
  -> (F * a |-> v)%pred (upd m a v).
(* hint proof tokens: 154 *)
Proof.
  unfold upd; unfold_sep_star; intros; repeat deex.
  exists m.
  exists (fun a' => if AEQ a' a then Some v else None).
  split; [|split].
  - apply functional_extensionality; intro.
    unfold mem_union; destruct (AEQ x a); subst; intuition.
    rewrite H0; auto.
    destruct (m x); auto.
  - unfold mem_disjoint in *. intuition. repeat deex.
    destruct (AEQ a0 a); subst; intuition; pred.
  - intuition; eauto.
    unfold ptsto; intuition.
    destruct (AEQ a a); pred.
    destruct (AEQ a' a); pred.
Qed.
Lemma ptsto_insert_disjoint: forall V (F : @pred AT AEQ V) a v m,
  F m -> m a = None
  -> (F * a |-> v)%pred (insert m a v).
Proof.
(* original proof tokens: 154 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_upd:
  forall a v v0 F (m : @mem AT AEQ V),
  (a |-> v0 * F)%pred m ->
  (a |-> v * F)%pred (upd m a v).
(* hint proof tokens: 177 *)
Proof.
  unfold upd; unfold_sep_star; intros; repeat deex.
  exists (fun a' => if AEQ a' a then Some v else None).
  exists m2.
  split; [|split].
  - apply functional_extensionality; intro.
    unfold mem_union; destruct (AEQ x a); eauto.
    destruct H1; repeat deex.
    rewrite H1; auto.
  - unfold mem_disjoint in *. intuition. repeat deex.
    apply H.
    destruct H1; repeat deex.
    repeat eexists; eauto.
    destruct (AEQ a0 a); subst; eauto.
    pred.
  - intuition eauto.
    unfold ptsto; intuition.
    destruct (AEQ a a); pred.
    destruct (AEQ a' a); pred.
Qed.
Lemma ptsto_updSome:
  forall a v v0 F (m : @mem AT AEQ V),
  (a |-> v0 * F)%pred m ->
  (a |-> v * F)%pred (updSome m a v).
Proof.
(* original proof tokens: 201 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_upd':
  forall a v v0 F (m : @mem AT AEQ V),
  (F * a |-> v0)%pred m ->
  (F * a |-> v)%pred (upd m a v).
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_upd_bwd:
  forall a b v w F (m : @mem AT AEQ V),
  a <> b ->
  (a |-> v * F)%pred (upd m b w) ->
  (a |-> v * any)%pred m.
Proof.
(* original proof tokens: 248 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_delete:
  forall a v0 F (m : @mem AT AEQ V),
  (a |-> v0 * F)%pred m ->
  F (delete m a).
Proof.
(* original proof tokens: 167 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_delete':
  forall a v0 F (m : @mem AT AEQ V),
  (F * a |-> v0)%pred m ->
  F (delete m a).
(* hint proof tokens: 25 *)
Proof.
  intros.
  eapply ptsto_delete.
  apply sep_star_comm.
  eauto.
Qed.
Lemma any_sep_star_ptsto : forall a v (m : @mem AT AEQ V),
  m a = Some v -> (any * a |-> v)%pred m.
Proof.
(* original proof tokens: 170 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_eq : forall (p1 p2 : @pred AT AEQ V) m a v1 v2,
  p1 m -> p2 m ->
  (exists F, p1 =p=> a |-> v1 * F) ->
  (exists F, p2 =p=> a |-> v2 * F) ->
  v1 = v2.
(* hint proof tokens: 63 *)
Proof.
  intros.
  repeat deex.
  apply H1 in H; clear H1.
  apply H2 in H0; clear H2.
  apply ptsto_valid in H.
  apply ptsto_valid in H0.
  repeat deex.
  congruence.
Qed.
Lemma ptsto_value_eq : forall a v1 v2,
  v1 = v2 -> (@pimpl AT AEQ V) (a |-> v1)%pred (a |-> v2)%pred.
Proof.
(* original proof tokens: 17 *)
apply pimpl_refl.
(* No more tactics to try *)
Admitted.

Lemma pimpl_and_split:
  forall (a b c : @pred AT AEQ V),
  (a =p=> b)
  -> (a =p=> c)
  -> (a =p=> b /\ c).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_and_lift: forall (a b: @pred AT AEQ V) (c:Prop),
  (a =p=> b)
  -> c
  -> (a =p=> b /\ [c]).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma pimpl_or_l: forall (a b c: @pred AT AEQ V),
  (a =p=> c)
  -> (b =p=> c)
  -> (a \/ b =p=> c).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma pimpl_or_r: forall (a b c: @pred AT AEQ V),
  ((a =p=> b) \/ (a =p=> c))
  -> (a =p=> b \/ c).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_or_apply : forall (a b : @pred AT AEQ V) m,
  (a \/ b)%pred m ->
  a m \/ b m.
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma pimpl_any :
  forall (p : @pred AT AEQ V),
  p =p=> any.
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 9 *)

firstorder.
Qed.

Lemma pimpl_emp_any :
  forall (p : @pred AT AEQ V),
  p =p=> emp * any.
(* hint proof tokens: 28 *)
Proof.
  intros.
  eapply pimpl_trans; [|apply pimpl_star_emp]; apply pimpl_any.
Qed.
Lemma eq_pimpl : forall (a b : @pred AT AEQ V),
  a = b
  -> (a =p=> b).
(* hint proof tokens: 13 *)
Proof.
  intros; subst; firstorder.
Qed.
Theorem sep_star_indomain : forall (p q : @pred AT AEQ V) a,
  (p =p=> indomain a) ->
  (p * q =p=> indomain a).
(* hint proof tokens: 45 *)
Proof.
  unfold_sep_star; unfold pimpl, indomain, mem_union.
  intros.
  repeat deex.
  edestruct H; eauto.
  rewrite H1.
  eauto.
Qed.
Theorem ptsto_indomain : forall (a : AT) (v : V),
  a |-> v =p=> (@indomain AT AEQ V) a.
Proof.
(* original proof tokens: 9 *)
pred.
(* No more tactics to try *)
Admitted.

Theorem sep_star_ptsto_some : forall a v F (m : @mem AT AEQ V),
  (a |-> v * F)%pred m -> m a = Some v.
Proof.
(* original proof tokens: 36 *)
(* generated proof tokens: 11 *)

apply ptsto_valid.
Qed.

Lemma sep_star_ptsto_some_eq : forall (m : @mem AT AEQ V) F a v v',
  (a |-> v * F)%pred m -> m a = Some v' -> v = v'.
(* hint proof tokens: 32 *)
Proof.
  intros.
  apply sep_star_ptsto_some in H.
  rewrite H in H0.
  inversion H0; auto.
Qed.
Theorem sep_star_ptsto_indomain : forall a v F (m : @mem AT AEQ V),
  (a |-> v * F)%pred m -> indomain a m.
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Theorem sep_star_or_distr : forall (a b c : @pred AT AEQ V),
  (a * (b \/ c))%pred <=p=> (a * b \/ a * c)%pred.
(* hint proof tokens: 123 *)
Proof.
  split.
  - unfold_sep_star; unfold pimpl, or.
    intros; repeat deex.
    + left. do 2 eexists. eauto.
    + right. do 2 eexists. eauto.
  - apply pimpl_or_l.
    + apply pimpl_sep_star; [apply pimpl_refl|].
      apply pimpl_or_r; left; apply pimpl_refl.
    + apply pimpl_sep_star; [apply pimpl_refl|].
      apply pimpl_or_r; right; apply pimpl_refl.
Qed.
Theorem sep_star_and_distr : forall (a b c : @pred AT AEQ V),
  (a * (b /\ c))%pred =p=> (a * b /\ a * c)%pred.
Proof.
(* original proof tokens: 32 *)
unfold piff, pimpl; unfold_sep_star; intros. 
pred.
unfold mem_union in *; repeat deex.
(* No more tactics to try *)
Admitted.

Theorem sep_star_and_distr' : forall (a b c : @pred AT AEQ V),
  ((b /\ c) * a)%pred =p=> (b * a /\ c * a)%pred.
Proof.
(* original proof tokens: 32 *)
unfold pimpl, and, sep_star. 
pred.
(* No more tactics to try *)
Admitted.

Lemma sep_star_lift_empty : forall AT AEQ V P Q,
  @pimpl AT AEQ V ([[ P ]] * [[ Q ]]) ([[ P /\ Q ]]).
(* hint proof tokens: 42 *)
Proof.
  unfold_sep_star; unfold pimpl, lift_empty, mem_union.
  firstorder; rewrite H.
  destruct (x a) eqn:?; try congruence.
Qed.
Lemma lift_empty_and_distr_l : forall AT AEQ V P Q (p q : @pred AT AEQ V),
  ([[ P ]] * p) /\ ([[ Q ]] * q) =p=> [[ P /\ Q ]] * (p /\ q).
(* hint proof tokens: 87 *)
Proof.
  unfold_sep_star; unfold pimpl, and, lift_empty, mem_union.
  intros; intuition; repeat deex.
  assert (m2 = m3).
  apply functional_extensionality; intros.
  apply equal_f with (x := x) in H1.
  rewrite H5, H8 in H1; auto.
  subst; do 2 eexists; intuition.
Qed.
Lemma lift_empty_and_distr_r : forall AT AEQ V P Q (p q : @pred AT AEQ V),
  (p * [[ P ]]) /\ (q * [[ Q ]]) =p=> (p /\ q) * [[ P /\ Q ]].
Proof.
(* original proof tokens: 92 *)
unfold piff; unfold_sep_star; pred.
unfold pimpl; pred.
eexists; eexists.
(* No more tactics to try *)
Admitted.

Theorem lift_impl : forall (P : @pred AT AEQ V) (Q : Prop), (forall m, P m -> Q) -> P =p=> [[ Q ]] * P.
Proof.
(* original proof tokens: 37 *)
apply pimpl_refl.
(* No more tactics to try *)
Admitted.

Lemma ptsto_conflict : forall a (m : @mem AT AEQ V),
  ~ (a |->? * a |->?)%pred m.
(* hint proof tokens: 14 *)
Proof.
  unfold_sep_star; firstorder discriminate.
Qed.
Lemma ptsto_conflict_F : forall a F (m : @mem AT AEQ V),
  ~ (a |->? * a |->? * F)%pred m.
Proof.
(* original proof tokens: 14 *)
(* generated proof tokens: 17 *)
firstorder.
unfold_sep_star; firstorder discriminate.
Qed.

Theorem ptsto_complete : forall a v (m1 m2 : @mem AT AEQ V),
  (a |-> v)%pred m1 -> (a |-> v)%pred m2 -> m1 = m2.
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

Theorem ptsto_diff_ne : forall a0 a1 v0 v1 F0 F1 (m : @mem AT AEQ V),
  (a0 |-> v0 * F0)%pred m ->
  (a1 |-> v1 * F1)%pred m ->
  v0 <> v1 ->
  a0 <> a1.
Proof.
(* original proof tokens: 40 *)
intros a0 a1 v0 v1 F0 F1 m H1 H2 H3.
(* No more tactics to try *)
Admitted.

Theorem emp_complete : forall m1 m2,
  (@emp AT AEQ V) m1 -> emp m2 -> m1 = m2.
(* hint proof tokens: 24 *)
Proof.
  intros.
  apply functional_extensionality; unfold emp in *; congruence.
Qed.
Theorem sep_star_empty_mem : forall (a b : @pred AT AEQ V),
  (a * b)%pred empty_mem -> a empty_mem /\ b empty_mem.
(* hint proof tokens: 150 *)
Proof.
  unfold_sep_star.
  intros.
  destruct H. destruct H. destruct H. destruct H0. destruct H1.
  cut (x = empty_mem).
  cut (x0 = empty_mem).
  intros; subst; intuition.

  unfold mem_union, empty_mem in *.
  apply functional_extensionality; intro fa.
  apply equal_f with (x:=fa) in H.
  destruct (x0 fa); auto.
  destruct (x fa); auto.
  inversion H.

  unfold mem_union, empty_mem in *.
  apply functional_extensionality; intro fa.
  apply equal_f with (x:=fa) in H.
  destruct (x fa); auto.
Qed.
Theorem ptsto_empty_mem : forall a v,
  ~ (a |-> v)%pred (@empty_mem AT AEQ V).
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Theorem emp_empty_mem :
  emp (@empty_mem AT AEQ V).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Theorem emp_empty_mem_only : forall (m : @mem AT AEQ V),
  emp m -> m = empty_mem.
(* hint proof tokens: 20 *)
Proof.
  intros; apply functional_extensionality; intros.
  firstorder.
Qed.
Theorem pred_empty_mem : forall (p : @pred AT AEQ V),
  p (@empty_mem AT AEQ V) ->
  emp =p=> p.
(* hint proof tokens: 27 *)
Proof.
  unfold pimpl; intros.
  apply emp_empty_mem_only in H0.
  subst; auto.
Qed.
Theorem emp_mem_union : forall (m1 m2 : @mem AT AEQ V),
  mem_union m1 m2 = empty_mem ->
  m1 = empty_mem /\ m2 = empty_mem.
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Theorem emp_pimpl_sep_star : forall (p q : @pred AT AEQ V),
  emp =p=> p * q ->
  (emp =p=> p) /\ (emp =p=> q).
(* hint proof tokens: 104 *)
Proof.
  unfold_sep_star.
  unfold pimpl; intros.
  intuition.

  specialize (H m H0); repeat deex.
  apply emp_empty_mem_only in H0.
  rewrite H0.
  apply emp_mem_union in H0; intuition; subst; auto.

  specialize (H m H0); repeat deex.
  apply emp_empty_mem_only in H0.
  rewrite H0.
  apply emp_mem_union in H0; intuition; subst; auto.
Qed.
Theorem emp_not_ptsto : forall a v,
  ~ ((@emp AT AEQ V) =p=> a |-> v)%pred.
(* hint proof tokens: 46 *)
Proof.
  unfold emp, ptsto, pimpl, not; intros.
  specialize (H empty_mem).
  edestruct H.
  firstorder.
  unfold empty_mem in *; congruence.
Qed.
Lemma mem_union_empty_mem : forall (m : @mem AT AEQ V),
  mem_union empty_mem m = m.
(* hint proof tokens: 24 *)
Proof.
  unfold mem_union; intros; apply functional_extensionality; intros.
  firstorder.
Qed.
Lemma mem_union_empty_mem' : forall (m : @mem AT AEQ V),
  mem_union m empty_mem = m.
Proof.
(* original proof tokens: 28 *)
(* generated proof tokens: 44 *)
unfold mem_union; intros; apply functional_extensionality; intros. 
firstorder.
unfold mem, empty_mem. 
destruct (m x) eqn:Hx; auto.
Qed.

Lemma mem_disjoint_empty_mem : forall (m : @mem AT AEQ V),
  mem_disjoint empty_mem m.
Proof.
(* original proof tokens: 26 *)
unfold mem_disjoint, empty_mem; intros. 
firstorder.
(* No more tactics to try *)
Admitted.

Theorem notindomain_empty_mem : forall a,
  notindomain a (@empty_mem AT AEQ V).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Theorem emp_notindomain : forall a (m : @mem AT AEQ V),
  emp m -> notindomain a m.
(* hint proof tokens: 22 *)
Proof.
  intros; unfold notindomain.
  pose proof (H a); auto.
Qed.
Theorem emp_pimpl_notindomain : forall a,
  emp =p=> (@notindomain AT AEQ V) a.
(* hint proof tokens: 21 *)
Proof.
  unfold pimpl; intros.
  apply emp_notindomain; auto.
Qed.
Theorem emp_mem_except : forall (m : @mem AT AEQ V) a,
  emp m -> emp (mem_except m a).
(* hint proof tokens: 25 *)
Proof.
  unfold emp, mem_except; intros.
  destruct (AEQ a0 a); auto.
Qed.
Theorem mem_except_double : forall (m : @mem AT AEQ V) a,
  mem_except (mem_except m a) a = mem_except m a.
Proof.
(* original proof tokens: 31 *)
(* generated proof tokens: 44 *)

unfold mem_except; intros. 
apply functional_extensionality; intro a0.
destruct (AEQ a0 a); destruct (AEQ a0 a); reflexivity.
Qed.

Lemma mem_except_is_none : forall AT AEQ V (m : @mem AT AEQ V) a,
  mem_except m a a = None.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Theorem mem_except_eq : forall (m : @mem AT AEQ V) a,
  mem_except m a a = None.
Proof.
(* original proof tokens: 23 *)
(* generated proof tokens: 34 *)
unfold mem_except; intros. 
destruct (AEQ a a); auto.
unfold mem in *; simpl in *; contradiction.
Qed.

Theorem mem_except_ne : forall (m : @mem AT AEQ V) a a',
  a <> a' ->
  mem_except m a a' = m a'.
Proof.
(* original proof tokens: 24 *)
(* generated proof tokens: 47 *)
unfold mem_except; intros; destruct (AEQ a' a); subst; auto.
destruct (m a) eqn:?.
exfalso.
apply H.
reflexivity.
firstorder.
Qed.

Theorem upd_mem_except : forall (m : @mem AT AEQ V) a v,
  upd (mem_except m a) a v = upd m a v.
(* hint proof tokens: 51 *)
Proof.
  intros; apply functional_extensionality; intros.
  destruct (AEQ a x); subst.
  repeat rewrite upd_eq by auto; auto.
  repeat rewrite upd_ne by auto; rewrite mem_except_ne; auto.
Qed.
Theorem insert_mem_except : forall (m : @mem AT AEQ V) a v v0,
  m a = Some v0 ->
  insert (mem_except m a) a v = upd m a v.
Proof.
(* original proof tokens: 53 *)

(* No more tactics to try *)
Admitted.

Theorem mem_except_upd : forall (m : @mem AT AEQ V) a v,
  mem_except (upd m a v) a = mem_except m a.
(* hint proof tokens: 33 *)
Proof.
  unfold mem_except, upd.
  intros; apply functional_extensionality; intros.
  destruct (AEQ x a); auto.
Qed.
Lemma mem_except_insert: forall (m : @mem AT AEQ V) a v,
  mem_except (insert m a v) a = mem_except m a.
(* hint proof tokens: 34 *)
Proof.
  unfold mem_except, insert.
  intros; apply functional_extensionality; intros.
  destruct (AEQ x a); eauto.
Qed.
Theorem mem_except_none : forall (m : @mem AT AEQ V) a,
  m a = None ->
  mem_except m a = m.
Proof.
(* original proof tokens: 34 *)
unfold mem_except, empty_mem; intros; apply functional_extensionality; intros; destruct (AEQ x a); eauto.
(* No more tactics to try *)
Admitted.

Lemma mem_except_union_comm: forall (m1 : @mem AT AEQ V) m2 a1 a2 v1,
  a1 <> a2
  -> (a1 |-> v1)%pred m1
  -> mem_except (mem_union m1 m2) a2 = mem_union m1 (mem_except m2 a2).
(* hint proof tokens: 85 *)
Proof.
  unfold mem_union, mem_except, ptsto.
  intuition.
  apply functional_extensionality; intros.
  destruct (AEQ x a2) eqn:Heq; auto.
  destruct (m1 x) eqn:Hx; auto; subst.
  pose proof (H2 a2 H) as Hy.
  rewrite Hx in Hy.
  inversion Hy.
Qed.
Lemma mem_disjoint_mem_except : forall (m1 : @mem AT AEQ V) m2 a,
  mem_disjoint m1 m2
  -> mem_disjoint m1 (mem_except m2 a).
(* hint proof tokens: 43 *)
Proof.
  unfold mem_disjoint, mem_except; intuition.
  repeat deex.
  destruct (AEQ a0 a).
  inversion H2.
  apply H.
  firstorder.
Qed.
Theorem notindomain_mem_union : forall a (m1 m2 : @mem AT AEQ V),
  notindomain a (mem_union m1 m2)
  <-> notindomain a m1 /\ notindomain a m2.
(* hint proof tokens: 49 *)
Proof.
  unfold notindomain, mem_union; split; intros; intuition.
  destruct (m1 a); auto.
  destruct (m1 a); auto.
  inversion H.
  rewrite H0; auto.
Qed.
Theorem notindomain_indomain_conflict : forall a (m : @mem AT AEQ V),
  notindomain a m -> indomain a m -> False.
(* hint proof tokens: 30 *)
Proof.
  unfold notindomain, indomain.
  firstorder.
  rewrite H in H0.
  inversion H0.
Qed.
Theorem notindomain_mem_except : forall a a' (m : @mem AT AEQ V),
  a <> a'
  -> notindomain a (mem_except m a')
  -> notindomain a m.
(* hint proof tokens: 27 *)
Proof.
  unfold notindomain, mem_except; intros.
  destruct (AEQ a a'); firstorder.
Qed.
Theorem notindomain_mem_except' : forall a a' (m : @mem AT AEQ V),
  notindomain a m
  -> notindomain a (mem_except m a').
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Theorem notindomain_mem_eq : forall a (m : @mem AT AEQ V),
  notindomain a m -> m = mem_except m a.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Theorem mem_except_notindomain : forall a (m : @mem AT AEQ V),
  notindomain a (mem_except m a).
(* hint proof tokens: 28 *)
Proof.
  unfold notindomain, mem_except; intros.
  destruct (AEQ a a); congruence.
Qed.
Theorem indomain_mem_except : forall a a' v (m : @mem AT AEQ V),
  a <> a'
  -> (mem_except m a') a = Some v
  -> m a = Some v.
(* hint proof tokens: 23 *)
Proof.
  unfold mem_except; intros.
  destruct (AEQ a a'); firstorder.
Qed.
Theorem notindomain_not_indomain : forall a (m : @mem AT AEQ V),
  notindomain a m <-> ~ indomain a m.
(* hint proof tokens: 44 *)
Proof.
  unfold notindomain, indomain; split; intros; destruct (m a);
    try congruence.
  destruct 1; discriminate.
  exfalso; eauto.
Qed.
Lemma indomain_upd_ne : forall (m : @mem AT AEQ V) a a' v,
  indomain a (upd m a' v)
  -> a <> a' -> indomain a m.
(* hint proof tokens: 32 *)
Proof.
  unfold indomain; intros.
  destruct H.
  rewrite upd_ne in H; auto.
  eexists; eauto.
Qed.
Theorem indomain_dec : forall a (m : @mem AT AEQ V),
  {indomain a m} + {notindomain a m}.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Theorem ptsto_mem_except : forall F a v (m : @mem AT AEQ V),
  (a |-> v * F)%pred m -> F (mem_except m a).
(* hint proof tokens: 102 *)
Proof.
  unfold ptsto; unfold_sep_star.
  intuition; repeat deex.
  replace ((mem_except (mem_union m1 m2) a)) with m2; auto.

  unfold mem_except.
  apply functional_extensionality; intro.
  destruct (AEQ x a); subst.
  eapply mem_disjoint_either; eauto.

  unfold mem_union.
  pose proof (H4 x); intuition.
  rewrite H1; simpl; auto.
Qed.
Theorem mem_except_ptsto : forall (F : @pred AT AEQ V) a v m,
  m a = Some v
  -> F (mem_except m a)
  -> (a |-> v * F)%pred m.
(* hint proof tokens: 146 *)
Proof.
  unfold indomain, ptsto; unfold_sep_star; intros.
  exists (fun a' => if (AEQ a' a) then Some v else None).
  exists (mem_except m a).
  split; [ | split].

  apply functional_extensionality; intro.
  unfold mem_union, mem_except.
  destruct (AEQ x a); subst; auto.

  unfold mem_disjoint, mem_except; intuition; repeat deex.
  destruct (AEQ a0 a); congruence.

  intuition.
  destruct (AEQ a a); subst; try congruence.
  destruct (AEQ a' a); subst; try congruence.
Qed.
Theorem indomain_mem_except_indomain : forall (m : @mem AT AEQ V) a a',
  indomain a (mem_except m a') -> indomain a m.
Proof.
(* original proof tokens: 60 *)

(* No more tactics to try *)
Admitted.

Theorem ptsto_mem_except_F : forall (F F' : @pred AT AEQ V) a a' v (m : @mem AT AEQ V),
  (a |-> v * F)%pred m
  -> a <> a'
  -> (forall m', F m' -> F' (mem_except m' a'))
  -> (a |-> v * F')%pred (mem_except m a').
Proof.
(* original proof tokens: 54 *)

(* No more tactics to try *)
Admitted.

Theorem ptsto_mem_except_exF : forall (F : @pred AT AEQ V) a a' v (m : @mem AT AEQ V),
  (a |-> v * F)%pred m
  -> a <> a'
  -> (a |-> v * (exists F', F'))%pred (mem_except m a').
(* hint proof tokens: 69 *)
Proof.
  unfold_sep_star.
  intros; repeat deex.
  eexists; exists (mem_except m2 a'); intuition eauto.
  eapply mem_except_union_comm; eauto.
  apply mem_disjoint_mem_except; auto.
  exists (diskIs (mem_except m2 a')). firstorder.
Qed.
Theorem mem_except_comm : forall (m : @mem AT AEQ V) a a',
  mem_except (mem_except m a) a' = mem_except (mem_except m a') a.
Proof.
(* original proof tokens: 89 *)

(* No more tactics to try *)
Admitted.

Theorem exact_domain_disjoint_union : forall (p : @pred AT AEQ V) m1 m2 m1' m2',
  exact_domain p ->
  mem_union m1 m2 = mem_union m1' m2' ->
  mem_disjoint m1 m2 ->
  mem_disjoint m1' m2' ->
  p m1 ->
  p m1' ->
  m1 = m1' /\ m2 = m2'.
Proof.
(* original proof tokens: 143 *)
intros p m1 m2 m1' m2' H_exact H_union H_disjoint H_disjoint' H_p1 H_p1'.
(* No more tactics to try *)
Admitted.

Theorem exact_domain_disjoint_union' : forall (p : @pred AT AEQ V) m1 m2 m1' m2',
  exact_domain p ->
  mem_union m1 m2 = mem_union m1' m2' ->
  mem_disjoint m1 m2 ->
  mem_disjoint m1' m2' ->
  p m2 ->
  p m2' ->
  m1 = m1' /\ m2 = m2'.
Proof.
(* original proof tokens: 61 *)
intros p m1 m2 m1' m2' H H0 H1 H2 H3 H4.
unfold exact_domain in H.
(* No more tactics to try *)
Admitted.

Theorem septract_sep_star :
  forall (p q : @pred AT AEQ V),
  exact_domain p ->
  (p --* (p * q) =p=> q)%pred.
(* hint proof tokens: 65 *)
Proof.
  unfold septract; unfold_sep_star; unfold pimpl; intros; repeat deex.
  rewrite mem_union_comm in H3 by eauto.
  apply mem_disjoint_comm in H1.
  edestruct exact_domain_disjoint_union; try eassumption.
  congruence.
Qed.
Theorem septract_pimpl_l :
  forall (p p' q : @pred AT AEQ V),
  (p =p=> p') ->
  (p --* q =p=> p' --* q).
(* hint proof tokens: 24 *)
Proof.
  unfold septract; unfold pimpl; intros; repeat deex.
  eauto.
Qed.
Theorem septract_pimpl_r :
  forall (p q q' : @pred AT AEQ V),
  (q =p=> q') ->
  (p --* q =p=> p --* q').
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Theorem strictly_exact_to_exact_domain : forall (p : @pred AT AEQ V),
  strictly_exact p -> exact_domain p.
(* hint proof tokens: 33 *)
Proof.
  unfold strictly_exact, exact_domain; intros.
  specialize (H m1 m2 H0 H1).
  subst; intuition.
Qed.
Theorem strictly_exact_to_precise : forall (p : @pred AT AEQ V),
  strictly_exact p -> precise p.
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Theorem ptsto_strictly_exact : forall a v,
  @strictly_exact AT AEQ V (a |-> v)%pred.
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

Theorem emp_strictly_exact : strictly_exact (@emp AT AEQ V).
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Theorem sep_star_exact_domain : forall (p q : @pred AT AEQ V),
  exact_domain p -> exact_domain q ->
  exact_domain (p * q)%pred.
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Theorem sep_star_strictly_exact : forall (p q : @pred AT AEQ V),
  strictly_exact p -> strictly_exact q ->
  strictly_exact (p * q)%pred.
(* hint proof tokens: 55 *)
Proof.
  unfold strictly_exact; unfold_sep_star; unfold mem_union; intros.
  repeat deex.
  specialize (H _ _ H4 H5).
  specialize (H0 _ _ H6 H8).
  subst.
  eauto.
Qed.
Hint Resolve mem_disjoint_assoc_1.
Hint Resolve mem_disjoint_assoc_2.
Hint Resolve mem_union_assoc.
Hint Resolve mem_disjoint_union.
Hint Resolve mem_disjoint_union_2.
Theorem sep_star_precise : forall (p q : @pred AT AEQ V),
  precise p -> precise q ->
  precise (p * q)%pred.
(* hint proof tokens: 265 *)
Proof.
  unfold precise; unfold_sep_star; intros; repeat deex.
  specialize (H m0 (mem_union m3 m2') m2 (mem_union m4 m1')).
  specialize (H0 m3 (mem_union m0 m2') m4 (mem_union m2 m1')).
  rewrite H; clear H; eauto.
  rewrite H0; clear H0; eauto.
  - rewrite <- mem_union_assoc; try apply mem_disjoint_comm; auto.
    rewrite <- mem_union_assoc; try apply mem_disjoint_comm; auto.
    rewrite <- (mem_union_comm H5).
    rewrite <- (mem_union_comm H4).
    auto.
    rewrite <- (mem_union_comm H4). apply mem_disjoint_comm. eauto.
    rewrite <- (mem_union_comm H5). apply mem_disjoint_comm. eauto.
  - rewrite (mem_union_comm H5) in H3.
    apply mem_disjoint_assoc_1; auto; try apply mem_disjoint_comm; auto.
  - rewrite (mem_union_comm H4) in H2.
    apply mem_disjoint_assoc_1; auto; try apply mem_disjoint_comm; auto.
  - repeat rewrite <- mem_union_assoc; auto.
Qed.
Theorem forall_strictly_exact : forall A (a : A) (p : A -> @pred AT AEQ V),
  (forall x, strictly_exact (p x)) ->
  strictly_exact (foral x, p x).
(* hint proof tokens: 25 *)
Proof.
  unfold foral_, strictly_exact; intros.
  specialize (H a).
  eauto.
Qed.
Lemma emp_pimpl_ptsto_exfalso : forall a v,
  ~ (@emp AT AEQ V =p=> a |-> v).
Proof.
(* original proof tokens: 43 *)
(* generated proof tokens: 12 *)

apply emp_not_ptsto.
Qed.

Lemma emp_pimpl_ptsto_exis_exfalso : forall a,
  ~ (@emp AT AEQ V =p=> a |->?).
(* hint proof tokens: 50 *)
Proof.
  unfold pimpl, ptsto, exis; intuition.
  specialize (H empty_mem).
  destruct H.
  apply emp_empty_mem.
  destruct H.
  unfold empty_mem in H; congruence.
Qed.
Lemma sep_star_ptsto_and_eq : forall (p q : @pred AT AEQ V) a v1 v2,
  (p * a |-> v1) /\ (q * a |-> v2) =p=> (p /\ q) * (a |-> v1) * [[ v1 = v2 ]].
Proof.
(* original proof tokens: 349 *)

(* No more tactics to try *)
Admitted.

End GenPredThm.
Instance piff_equiv {AT AEQ V} :
  Equivalence (@piff AT AEQ V).
Proof.
(* original proof tokens: 42 *)
(* generated proof tokens: 13 *)

split; intros; firstorder.
Qed.

Instance pimpl_preorder {AT AEQ V} :
  PreOrder (@pimpl AT AEQ V).
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Instance piff_pimpl_subrelation {AT AEQ V} :
  subrelation (@piff AT AEQ V) (@pimpl AT AEQ V).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance piff_flip_pimpl_subrelation {AT AEQ V} :
  subrelation (@piff AT AEQ V) (Basics.flip (@pimpl AT AEQ V)).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Instance pimpl_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> Basics.flip Basics.impl) (@pimpl AT AEQ V).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Instance pimpl_pimpl_proper1 {AT AEQ V} :
  Proper (pimpl ==> Basics.flip pimpl ==> Basics.flip Basics.impl) (@pimpl AT AEQ V).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance pimpl_pimpl_proper2 {AT AEQ V} :
  Proper (Basics.flip pimpl ==> pimpl ==> Basics.impl) (@pimpl AT AEQ V).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Instance sep_star_apply_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> eq ==> Basics.impl) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 49 *)
unfold Proper, sep_star; intros; subst; unfold sep_star_impl; unfold pimpl in *; intros; pred; repeat deex; eauto.
unfold Proper, respectful, sep_star; intros.
unfold sep_star_impl in *; intros.
repeat deex; eauto.
(* No more tactics to try *)
Admitted.

Instance sep_star_apply_pimpl_proper' {AT AEQ V} :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl ==> eq ==> Basics.flip Basics.impl) (@sep_star AT AEQ V).
(* hint proof tokens: 49 *)
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  apply pimpl_sep_star; assumption.
Qed.
Instance sep_star_apply_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> eq ==> Basics.impl) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 57 *)
unfold sep_star; unfold pimpl; intros.
unfold_sep_star; intuition.
(* No more tactics to try *)
Admitted.

Instance sep_star_apply_piff_proper' {AT AEQ V} :
  Proper (piff ==> piff ==> eq ==> iff) (@sep_star AT AEQ V).
(* hint proof tokens: 83 *)
Proof.
  intros p p' Hp q q' Hq m m' Hm.
  subst; split; intros.
  - eapply pimpl_apply; [| eassumption ]. apply pimpl_sep_star. apply Hp. apply Hq.
  - eapply pimpl_apply; [| eassumption ]. apply pimpl_sep_star. apply Hp. apply Hq.
Qed.
Instance sep_star_apply_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq ==> eq) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 10 *)
unfold Proper, sep_star; intros.
unfold mem_union, mem_disjoint in *.
intros; repeat deex; eauto.
(* No more tactics to try *)
Admitted.

Instance sep_star_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 25 *)

unfold Proper, respectful, sep_star; intros.
rewrite H, H0; auto.
Qed.

Instance sep_star_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> piff) (@sep_star AT AEQ V).
(* hint proof tokens: 33 *)
Proof.
  intros a b H c d H'.
  split; ( apply pimpl_sep_star; [ apply H | apply H' ] ).
Qed.
Instance sep_star_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@sep_star AT AEQ V).
(* hint proof tokens: 23 *)
Proof.
  intros a b H c d H'.
  apply pimpl_sep_star; assumption.
Qed.
Instance sep_star_pimpl_proper' {AT AEQ V} :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl ==> Basics.flip pimpl) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 23 *)
unfold sep_star; unfold pimpl; intros.
unfold_sep_star; intros; repeat deex; eauto.
unfold Proper, respectful.
intros.
unfold sep_star in H.
repeat deex.
eexists; eexists; repeat split; auto.
(* No more tactics to try *)
Admitted.

Instance and_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq) (@and AT AEQ V).
Proof.
(* original proof tokens: 10 *)

(* No more tactics to try *)
Admitted.

Instance and_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> piff) (@and AT AEQ V).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance and_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@and AT AEQ V).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Instance or_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq) (@or AT AEQ V).
Proof.
(* original proof tokens: 10 *)

(* No more tactics to try *)
Admitted.

Instance or_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> piff) (@or AT AEQ V).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance or_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@or AT AEQ V).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Example pimpl_rewrite : forall AT AEQ V a b (p : @pred AT AEQ V) q x y, p =p=> q
  -> (x /\ a * p * b \/ y =p=> x /\ a * q * b \/ y).
(* hint proof tokens: 16 *)
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.
Instance exists_proper_eq {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A eq ==> eq) (@exis AT AEQ V A).
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Instance exists_proper_piff {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A piff ==> piff) (@exis AT AEQ V A).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Instance exists_proper_pimpl {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A pimpl ==> pimpl) (@exis AT AEQ V A).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Example pimpl_exists_rewrite : forall AT AEQ V (p : @pred AT AEQ V) q, p =p=> q
  -> (exists x, p * x) =p=> (exists x, q * x).
(* hint proof tokens: 19 *)
Proof.
  intros.
  setoid_rewrite H.
  reflexivity.
Qed.
Instance exists_proper_pimpl_impl {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A piff ==> eq ==> iff) (@exis AT AEQ V A).
(* hint proof tokens: 51 *)
Proof.
  intros a b Hab m1 m2 Hm.
  split; unfold Basics.impl, exis; intros; deex; eexists.
  eapply Hab; eauto.
  eapply Hab; eauto.
Qed.
Instance lift_empty_proper_iff {AT AEQ V} :
  Proper (iff ==> @piff _ _ _) (@lift_empty AT AEQ V).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Instance lift_empty_proper_impl {AT AEQ V} :
  Proper (Basics.impl ==> @pimpl _ _ _) (@lift_empty AT AEQ V).
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 16 *)

intros; unfold lift_empty; firstorder.
Qed.

Instance lift_empty_proper_eq {AT AEQ V} :
  Proper (eq ==> eq) (@lift_empty AT AEQ V).
Proof.
(* original proof tokens: 10 *)
unfold lift_empty; intros; auto.
(* No more tactics to try *)
Admitted.

Instance lift_empty_proper_expanded_impl {AT AEQ V} :
  Proper (Basics.impl ==> eq ==> Basics.impl) (@lift_empty AT AEQ V).
(* hint proof tokens: 28 *)
Proof.
  unfold lift_empty.
  intros a b Hab m1 m2 Hm H; subst.
  intuition.
Qed.
Instance lift_empty_proper_expanded_flipimpl {AT AEQ V} :
  Proper (Basics.flip Basics.impl ==> eq ==> Basics.flip Basics.impl) (@lift_empty AT AEQ V).
Proof.
(* original proof tokens: 28 *)
(* generated proof tokens: 32 *)

unfold lift_empty; intros P Q HPQ m1 m2 Hm H; subst; simpl in *; intuition.
Qed.

Instance lift_empty_proper_expanded_iff {AT AEQ V} :
  Proper (iff ==> eq ==> iff) (@lift_empty AT AEQ V).
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Instance funext_subrelation {A f R} {subf : subrelation R eq}:
  subrelation (@pointwise_relation A f R) eq.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Global Program Instance eq_equivalence {A} : Equivalence (@eq A) | 0.
Instance pred_apply_pimpl_proper {AT AEQ V} :
  Proper (eq ==> pimpl ==> Basics.impl) (@pred_apply AT AEQ V).
(* hint proof tokens: 29 *)
Proof.
  unfold pred_apply.
  intros ma mb Hmab p q Hpq H.
  subst.
  auto.
Qed.
Instance pred_apply_pimpl_flip_proper {AT AEQ V} :
  Proper (eq ==> Basics.flip pimpl ==> Basics.flip Basics.impl) (@pred_apply AT AEQ V).
(* hint proof tokens: 29 *)
Proof.
  unfold pred_apply.
  intros ma mb Hmab p q Hpq H.
  subst.
  auto.
Qed.
Instance pred_apply_piff_proper {AT AEQ V} :
  Proper (eq ==> piff ==> iff) (@pred_apply AT AEQ V).
(* hint proof tokens: 32 *)
Proof.
  unfold pred_apply.
  intros ma mb Hmab p q Hpq.
  subst. destruct Hpq.
  intuition.
Qed.
Example pred_apply_rewrite : forall AT AEQ V p q (m : @mem AT AEQ V),
  m ## p*q -> m ## q*p.
(* hint proof tokens: 20 *)
Proof.
  intros.
  rewrite sep_star_comm1 in H.
  auto.
Qed.
Theorem diskIs_extract : forall AT AEQ V a v (m : @mem AT AEQ V),
  (exists F, F * a |-> v)%pred m
  -> (diskIs m =p=> diskIs (mem_except m a) * a |-> v).
(* hint proof tokens: 181 *)
Proof.
  intros.
  destruct H.
  apply sep_star_comm in H. apply ptsto_valid in H.
  unfold pimpl, diskIs, ptsto; unfold_sep_star; intros; subst.
  exists (fun a' => if AEQ a' a then None else m0 a').
  exists (fun a' => if AEQ a' a then Some v else None).
  intuition.
  - unfold mem_union; apply functional_extensionality; intros.
    destruct (AEQ x0 a); subst; auto.
    destruct (m0 x0); auto.
  - unfold mem_disjoint; unfold not; intros. repeat deex.
    destruct (AEQ a0 a); discriminate.
  - destruct (AEQ a a); congruence.
  - destruct (AEQ a' a); subst; congruence.
Qed.
Theorem diskIs_extract' : forall AT AEQ V a v (m : @mem AT AEQ V),
  m a = Some v
  -> (diskIs m =p=> diskIs (mem_except m a) * a |-> v).
(* hint proof tokens: 36 *)
Proof.
  intros.
  unfold pimpl, diskIs; intros; subst.
  apply sep_star_comm.
  apply mem_except_ptsto; eauto.
Qed.
Theorem diskIs_combine_upd : forall AT AEQ V a v (m : @mem AT AEQ V),
  diskIs (mem_except m a) * a |-> v =p=> diskIs (upd m a v).
(* hint proof tokens: 118 *)
Proof.
  unfold pimpl, diskIs, ptsto, upd; unfold_sep_star; intros; subst; repeat deex.
  apply functional_extensionality; intros.
  case_eq (AEQ x a); intros; subst.
  - rewrite mem_union_comm; auto.
    erewrite mem_union_addr; eauto.
    apply mem_disjoint_comm; auto.
  - unfold mem_union, mem_except.
    destruct (AEQ x a); try discriminate.
    case_eq (m x); auto; intros.
    rewrite H4; auto.
Qed.
Theorem diskIs_combine_same : forall AT AEQ V a v (m : @mem AT AEQ V),
  (exists F, F * a |-> v)%pred m
  -> diskIs (mem_except m a) * a |-> v =p=> diskIs m.
(* hint proof tokens: 103 *)
Proof.
  intros.
  destruct H.
  apply sep_star_comm in H. apply ptsto_valid in H.
  unfold pimpl, diskIs, ptsto, upd; unfold_sep_star; intros; subst; repeat deex.
  apply functional_extensionality; intros.
  unfold mem_union, mem_except.
  destruct (AEQ x0 a); subst; try congruence.
  destruct (m x0); auto.
  rewrite H5; auto; discriminate.
Qed.
Theorem diskIs_pred : forall AT AEQ V (m : @mem AT AEQ V) (p : @pred AT AEQ V),
  p m ->
  diskIs m =p=> p.
Proof.
(* original proof tokens: 20 *)

(* No more tactics to try *)
Admitted.

Definition pred_except AT AEQ V (F : @pred AT AEQ V) a v : @pred AT AEQ V :=
  fun m => m a = None /\ F (insert m a v).
Instance pred_except_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> eq ==> eq ==> pimpl) (@pred_except AT AEQ V).
(* hint proof tokens: 27 *)
Proof.
  intros F F' HF a a' Ha v v' Hv.
  subst.
  firstorder.
Qed.
Instance pred_except_piff_proper {AT AEQ V} :
  Proper (piff ==> eq ==> eq ==> piff) (@pred_except AT AEQ V).
Proof.
(* original proof tokens: 27 *)
unfold pred_except; intros.
split; intros; destruct H; subst; intuition.
(* No more tactics to try *)
Admitted.

Lemma pred_except_mem_except : forall AT AEQ V (F : @pred AT AEQ V) m a v,
  F m -> m a = Some v -> (pred_except F a v) (mem_except m a).
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma pred_except_ptsto : forall AT AEQ V (p q : @pred AT AEQ V) a v,
  (p =p=> q * a |-> v) ->
  (p =p=> pred_except p a v * a |-> v).
(* hint proof tokens: 75 *)
Proof.
  intros; rewrite sep_star_comm.
  unfold pimpl; intros.
  assert (m a = Some v).
  specialize (H m H0).
  eapply ptsto_valid.
  eapply sep_star_comm.
  eauto.
  eapply mem_except_ptsto; auto.
  apply pred_except_mem_except; eauto.
Qed.
Theorem pred_except_sep_star_ptsto : forall AT AEQ V (p : @pred AT AEQ V) a v a' v',
  a <> a' ->
  pred_except (p * a' |-> v') a v <=p=> pred_except p a v * a' |-> v'.
Proof.
(* original proof tokens: 449 *)

(* No more tactics to try *)
Admitted.

Theorem pred_except_sep_star_ptsto' : forall AT AEQ V (p : @pred AT AEQ V) a v,
  pred_except (p * a |-> v) a v =p=> p.
(* hint proof tokens: 166 *)
Proof.
  unfold pimpl, pred_except.
  unfold_sep_star; intros; intuition; repeat deex.
  assert (m = m1); try congruence.
  apply functional_extensionality; intros.
  destruct (AEQ x a); subst.
  - rewrite H0.
    case_eq (m1 a); intros; try auto.
    exfalso.
    apply H.
    exists a. do 2 eexists. intuition eauto.
    unfold ptsto in H4; intuition eauto.
  - apply equal_f with (x := x) in H1.
    rewrite insert_ne in H1 by auto.
    rewrite H1.
    unfold mem_union.
    destruct (m1 x); auto.
    unfold ptsto in H4; intuition.
Qed.
Theorem pred_except_sep_star_ptsto_notindomain : forall AT AEQ V (p : @pred AT AEQ V) a v,
  (p =p=> notindomain a) ->
  p =p=> pred_except (p * a |-> v) a v.
(* hint proof tokens: 153 *)
Proof.
  unfold pimpl, pred_except.
  unfold_sep_star; intros; intuition; repeat deex.
  - apply H; auto.
  - exists m.
    exists (Mem.insert empty_mem a v).
    assert (mem_disjoint m (insert empty_mem a v)).
    {
      apply mem_disjoint_comm.
      apply mem_disjoint_insert_l.
      eapply mem_disjoint_empty_mem.
      apply H; auto.
    }
    intuition eauto.
    rewrite mem_union_comm by eauto.
    rewrite <- mem_union_insert_comm; try reflexivity.
    apply H; auto.
    apply star_emp_pimpl.
    apply ptsto_insert_disjoint.
    apply emp_empty_mem.
    reflexivity.
Qed.
Lemma ptsto_insert_disjoint_ne: forall AT AEQ V (F : @pred AT AEQ V) a v a' v' m,
  a <> a' ->
  m a' = None ->
  (pred_except F a' v' * a |-> v)%pred m ->
  (F * a |-> v)%pred (insert m a' v').
Proof.
(* original proof tokens: 79 *)

(* No more tactics to try *)
Admitted.

Lemma pred_except_ptsto_pimpl : forall AT AEQ V (m : @mem AT AEQ V) off v F,
  (F * off |-> v)%pred m ->
  pred_except (diskIs m) off v =p=> F.
(* hint proof tokens: 170 *)
Proof.
  unfold_sep_star.
  unfold pimpl, diskIs, pred_except; intros.
  repeat deex.
  assert (m0 = m1); try congruence.
  apply functional_extensionality; intros.
  destruct (AEQ x off); subst.
  - rewrite H1.
    case_eq (m1 off); intros; auto.
    exfalso.
    apply H.
    exists off. do 2 eexists.
    intuition eauto.
    unfold ptsto in H4; intuition eauto.
  - eapply equal_f with (x := x) in H0.
    rewrite insert_ne in H0 by auto.
    rewrite H0.
    unfold mem_union.
    destruct (m1 x); auto.
    unfold ptsto in H4; intuition.
Qed.
Lemma ptsto_upd_bwd_or :
  forall AT AEQ V F a v v' (m : @mem AT AEQ V),
  (a |-> v' * F)%pred (upd m a v) ->
  F m \/ exists v0, (a |-> v0 * F)%pred m.
(* hint proof tokens: 87 *)
Proof.
  intros.
  case_eq (m a); intros.
  - right.
    exists v0.
    apply ptsto_mem_except in H.
    rewrite mem_except_upd in H.
    eapply mem_except_ptsto; eauto.
  - left.
    apply ptsto_mem_except in H.
    rewrite mem_except_upd in H.
    rewrite mem_except_none in H; auto.
Qed.
Lemma ptsto_insert_bwd :
  forall AT AEQ V F a v v' (m : @mem AT AEQ V),
  m a = None ->
  (a  |-> v' * F)%pred (insert m a v) ->
  F m.
(* hint proof tokens: 38 *)
Proof.
  intros.
  apply ptsto_mem_except in H0.
  rewrite mem_except_insert in H0.
  rewrite mem_except_none in H0; auto.
Qed.
Lemma ptsto_insert_bwd_ne: forall AT AEQ V (F : @pred AT AEQ V) a v a' v' m,
  a <> a' ->
  m a' = None ->
  (F * a |-> v)%pred (insert m a' v') ->
  (pred_except F a' v' * a |-> v)%pred m.
(* hint proof tokens: 298 *)
Proof.
  unfold_sep_star; unfold pimpl, pred_except; intros.
  repeat deex.
  exists (mem_except m1 a').
  exists m2.
  intuition.
  apply functional_extensionality; intros.
  - apply equal_f with (x := x) in H2.
    destruct (AEQ x a'); subst.
    rewrite H0 in *.
    rewrite mem_union_sel_none; auto.
    apply mem_except_is_none.
    unfold ptsto in H5.
    destruct H5.
    apply H5; eauto.
    unfold mem_union in *.
    rewrite mem_except_ne by auto.
    rewrite <- H2.
    rewrite insert_ne; auto.
  - apply mem_disjoint_comm.
    apply mem_disjoint_mem_except; eauto.
    apply mem_disjoint_comm; auto.
  - apply mem_except_is_none.
  - assert (m1 = insert (mem_except m1 a') a' v').
    apply functional_extensionality; intros.
    apply equal_f with (x := x) in H2.
    destruct (AEQ x a'); subst.
    rewrite insert_eq in *; auto.
    rewrite H2.
    rewrite mem_union_sel_l; auto.
    eapply ptsto_ne; eauto.
    apply mem_except_is_none.
    rewrite insert_ne; auto.
    rewrite mem_except_ne; auto.
    rewrite <- H4; auto.
Qed.
Lemma sep_star_split_l: forall AT AEQ V F (x: @pred AT AEQ V) y m,
  (F * x * y)%pred m -> 
  exists F1, (F1 * x)%pred m.
Proof.
(* original proof tokens: 41 *)
unfold sep_star in *; intros; repeat deex; eexists; intuition.
(* No more tactics to try *)
Admitted.

Lemma pimpl_sep_star_split_l: forall AT AEQ V F1 F2 (x: @pred AT AEQ V) y m,
    (F1 * x * y) %pred m ->
    (F1 * y) =p=> F2 ->
    (F1 * x) * y =p=> F2 * x.
(* hint proof tokens: 47 *)
Proof.
  intros.
  erewrite sep_star_assoc_1.
  setoid_rewrite sep_star_comm at 2.
  erewrite sep_star_assoc_2.
  erewrite H0; eauto.
Qed.
Lemma pimpl_sep_star_split_r: forall AT AEQ V F1 F2 (x: @pred AT AEQ V) y m,
    (F1 * x * y) %pred m ->
    (F1 * x) =p=> F2 ->
    (F1 * y) * x =p=> F2 * y.
(* hint proof tokens: 47 *)
Proof.
  intros.
  erewrite sep_star_assoc_1.
  setoid_rewrite sep_star_comm at 2.
  erewrite sep_star_assoc_2.
  erewrite H0; eauto.
Qed.
Lemma sep_star_notindomain : forall AT AEQ V (p q : @pred AT AEQ V) a,
  p =p=> notindomain a ->
  q =p=> notindomain a ->
  p * q =p=> notindomain a.
(* hint proof tokens: 47 *)
Proof.
  unfold_sep_star.
  unfold notindomain, pimpl.
  intros; repeat deex.
  unfold mem_union.
  rewrite H by assumption.
  rewrite H0 by assumption.
  auto.
Qed.
Lemma ptsto_notindomain : forall AT AEQ V a a' v,
  a <> a' ->
  a |-> v =p=> (@notindomain AT AEQ V) a'.
(* hint proof tokens: 19 *)
Proof.
  unfold pimpl, ptsto, notindomain; intuition.
Qed.
Lemma sep_star_none : forall AT AEQ V (p q : @pred AT AEQ V) a,
  (forall m, p m -> m a = None) ->
  (forall m, q m -> m a = None) ->
  forall m, (p * q)%pred m ->
  m a = None.
Proof.
(* original proof tokens: 50 *)
(* generated proof tokens: 15 *)

apply sep_star_notindomain; auto.
Qed.

Lemma ptsto_none : forall AT AEQ V a a' v (m : @mem AT AEQ V),
  a <> a' ->
  (a |-> v)%pred m ->
  m a' = None.
(* hint proof tokens: 12 *)
Proof.
  unfold ptsto; intuition.
Qed.
Global Opaque pred.
