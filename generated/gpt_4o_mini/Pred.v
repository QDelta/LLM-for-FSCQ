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
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 8 *)

(* No more tactics to try *)
Admitted.

Hint Resolve pimpl_refl.
Theorem mem_disjoint_comm:
  forall (m1 m2 : @mem AT AEQ V),
  mem_disjoint m1 m2 <-> mem_disjoint m2 m1.
Proof.
(* original proof tokens: 26 *)
split; intro H; unfold mem_disjoint in *; unfold not in *; intros; apply H; auto.
(* No more tactics to try *)
Admitted.

Theorem mem_disjoint_assoc_1:
  forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint m1 m2 ->
  mem_disjoint (mem_union m1 m2) m3 ->
  mem_disjoint m1 (mem_union m2 m3).
Proof.
(* original proof tokens: 66 *)
unfold mem_disjoint in *; intros H1 H2; subst.
intros m3 Hnot_exists_1 Hnot_exists_2.
apply mem_disjoint_comm in Hnot_exists_1.
apply mem_disjoint_comm in Hnot_exists_1.
apply mem_disjoint_comm in Hnot_exists_2.
apply mem_disjoint_comm in Hnot_exists_2.
apply mem_disjoint_comm in Hnot_exists_1.
(* No more tactics to try *)
Admitted.

Theorem mem_disjoint_assoc_2:
  forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint m2 m3 ->
  mem_disjoint m1 (mem_union m2 m3) ->
  mem_disjoint (mem_union m1 m2) m3.
Proof.
(* original proof tokens: 81 *)
unfold mem_disjoint.
intros m1 m2 m3 H1 H2.
intro H.
destruct H.
apply H1.
destruct H.
destruct H.
destruct H.
destruct H1.
destruct H.
destruct H0 as [v1 H0].
apply mem_disjoint_comm in H2.
exfalso.
apply H2.
firstorder.
destruct (H x).
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
unfold mem_disjoint.
firstorder.
(* No more tactics to try *)
Admitted.

Theorem mem_disjoint_upd:
  forall (m1 m2 : @mem AT AEQ V) a v v0,
  m1 a = Some v0 ->
  mem_disjoint m1 m2 ->
  mem_disjoint (upd m1 a v) m2.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma mem_disjoint_either:
  forall (m1 m2 : @mem AT AEQ V) a v,
  mem_disjoint m1 m2
  -> m1 a = Some v -> m2 a = None.
Proof.
(* original proof tokens: 58 *)

(* No more tactics to try *)
Admitted.

Lemma mem_disjoint_insert_l : forall (m1 m2 : @mem AT AEQ V) a v,
  mem_disjoint m1 m2 ->
  m2 a = None ->
  mem_disjoint (insert m1 a v) m2.
Proof.
(* original proof tokens: 68 *)
unfold mem_disjoint, insert.
(* No more tactics to try *)
Admitted.

Theorem mem_union_comm:
  forall (m1 m2 : @mem AT AEQ V),
  mem_disjoint m1 m2 ->
  mem_union m1 m2 = mem_union m2 m1.
Proof.
(* original proof tokens: 50 *)
unfold mem_union.
unfold mem_disjoint in *; intros; extensionality a.
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
Proof.
(* original proof tokens: 22 *)
(* generated proof tokens: 25 *)
unfold mem_union, mem_disjoint in *; intros.
rewrite H0.
reflexivity.
Qed.

Theorem mem_union_upd:
  forall (m1 m2 : @mem AT AEQ V) a v,
  mem_union (upd m1 a v) m2 = upd (mem_union m1 m2) a v.
Proof.
(* original proof tokens: 33 *)
unfold mem_union.
(* No more tactics to try *)
Admitted.

Theorem mem_union_assoc:
  forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint m1 m2 ->
  mem_disjoint (mem_union m1 m2) m3 ->
  mem_union (mem_union m1 m2) m3 = mem_union m1 (mem_union m2 m3).
Proof.
(* original proof tokens: 33 *)
unfold mem_union. intros m1 m2 m3 Hdis1 Hdis2. 
pred_unfold.
(* No more tactics to try *)
Admitted.

Lemma mem_union_sel_none : forall (m1 m2 : @mem AT AEQ V) a,
  m1 a = None ->
  m2 a = None ->
  mem_union m1 m2 a = None.
Proof.
(* original proof tokens: 23 *)
(* generated proof tokens: 22 *)

unfold mem_union. intros. rewrite H, H0. reflexivity.
Qed.

Lemma mem_union_none_sel : forall (m1 m2 : @mem AT AEQ V) a,
  mem_union m1 m2 a = None ->
  m1 a = None /\  m2 a = None.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma mem_union_sel_l : forall (m1 m2 : @mem AT AEQ V) a,
  mem_disjoint m1 m2 ->
  m2 a = None ->
  mem_union m1 m2 a = m1 a.
Proof.
(* original proof tokens: 23 *)
unfold mem_disjoint, mem_union in *; intros. 
simpl in *.
rewrite H0.
(* No more tactics to try *)
Admitted.

Lemma mem_union_sel_r : forall (m1 m2 : @mem AT AEQ V) a,
  mem_disjoint m1 m2 ->
  m1 a = None ->
  mem_union m1 m2 a = m2 a.
Proof.
(* original proof tokens: 28 *)
unfold mem_disjoint. intros. unfold mem_union. destruct (m1 a) eqn:Hm1.
destruct Hm1.
(* No more tactics to try *)
Admitted.

Lemma mem_union_insert_comm : forall (m1 m2 : @mem AT AEQ V) a v,
  m1 a = None ->
  m2 a = None ->
  insert (mem_union m1 m2) a v = mem_union (insert m1 a v) m2.
Proof.
(* original proof tokens: 53 *)
unfold insert.
(* No more tactics to try *)
Admitted.

Lemma mem_disjoint_mem_union_split_l : forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint m1 m3 ->
  mem_disjoint m2 m3 ->
  mem_disjoint (mem_union m1 m2) m3.
Proof.
(* original proof tokens: 68 *)
unfold mem_disjoint, mem_union.
intros m1 m2 m3 H1 H2 H3.
apply H2.
deex.
destruct H.
destruct H as [v2 H].
destruct H as [v1 H].
destruct H2.
destruct H.
destruct H1.
destruct (m1 a) eqn: Heqm1.
destruct (m3 a) eqn: Heqm3.
destruct Heqm3.
destruct (m3 a) eqn: Heqm3.
destruct (m2 a) eqn: Heqm2.
destruct Heqm3.
destruct Heqm2.
destruct Heqm1.
(* No more tactics to try *)
Admitted.

Lemma mem_disjoint_mem_union_split_r : forall (m1 m2 m3 : @mem AT AEQ V),
  mem_disjoint m1 m2 ->
  mem_disjoint m1 m3 ->
  mem_disjoint m1 (mem_union m2 m3).
Proof.
(* original proof tokens: 43 *)
unfold mem_disjoint, mem_union.
intuition.
deex.
deex.
deex.
destruct H3.
destruct H.
assert (H3: exists (x:AT) (v1 v2: V), m1 x = Some v1 /\ m2 x = Some v2).
(* No more tactics to try *)
Admitted.

Theorem sep_star_comm1:
  forall (p1 p2 : @pred AT AEQ V),
  (p1 * p2 =p=> p2 * p1)%pred.
Proof.
(* original proof tokens: 41 *)
unfold sep_star. 
rewrite sep_star_is. 
unfold sep_star_impl. 
pred.
(* No more tactics to try *)
Admitted.

Theorem sep_star_comm:
  forall (p1 p2 : @pred AT AEQ V),
  (p1 * p2 <=p=> p2 * p1)%pred.
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Theorem sep_star_assoc_1:
  forall (p1 p2 p3 : @pred AT AEQ V),
  (p1 * p2 * p3 =p=> p1 * (p2 * p3))%pred.
Proof.
(* original proof tokens: 73 *)
unfold sep_star. rewrite sep_star_is. unfold sep_star_impl.
pred.
(* No more tactics to try *)
Admitted.

Theorem sep_star_assoc_2:
  forall (p1 p2 p3 : @pred AT AEQ V),
  (p1 * (p2 * p3) =p=> p1 * p2 * p3)%pred.
Proof.
(* original proof tokens: 150 *)
unfold_sep_star.
apply pimpl_refl.
(* No more tactics to try *)
Admitted.

Theorem sep_star_assoc:
  forall (p1 p2 p3 : @pred AT AEQ V),
  (p1 * p2 * p3 <=p=> p1 * (p2 * p3))%pred.
Proof.
(* original proof tokens: 24 *)
unfold sep_star. 
rewrite sep_star_is. 
unfold sep_star_impl. 
intros p1 p2 p3. 
pred.
apply pimpl_refl.
(* No more tactics to try *)
Admitted.

Theorem sep_star_mem_union :
  forall (p q : @pred AT AEQ V) mp mq,
  mem_disjoint mp mq ->
  p mp -> q mq ->
  (p * q)%pred (mem_union mp mq).
Proof.
(* original proof tokens: 21 *)
firstorder.
unfold sep_star.
(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_exists_r_star:
  forall T p (q : @pred AT AEQ V),
  (exists x:T, p x * q) =p=> ((exists x:T, p x) * q).
Proof.
(* original proof tokens: 36 *)
unfold sep_star; rewrite sep_star_is; unfold sep_star_impl.
destruct 1 as [x H].
deex.
deex.
(* No more tactics to try *)
Admitted.

Lemma pimpl_exists_r_star_r:
  forall T (p : T -> pred) (q : @pred AT AEQ V),
  (exists x : T, p x) * q =p=>  (exists x : T, p x * q).
Proof.
(* original proof tokens: 36 *)
unfold sep_star. pred.
unfold_sep_star. pred.
eapply pimpl_exists_l_star.
unfold sep_star. pred.
apply pimpl_exists_l.
unfold_sep_star. pred.
eapply pimpl_exists_l_star.
unfold sep_star. pred.
apply pimpl_exists_l.
apply pimpl_exists_l_star.
apply sep_star_comm.
apply sep_star_mem_union.
(* Reached max number of model calls *)
Admitted.

Lemma pimpl_exists_l_star_r:
  forall T (p : T -> pred) (q : @pred AT AEQ V),
  q * (exists x : T, p x) =p=>  (exists x : T, q * p x).
Proof.
(* original proof tokens: 36 *)
unfold_sep_star; pred.
apply pimpl_exists_l.
(* No more tactics to try *)
Admitted.

Lemma pimpl_exists_and_l:
  forall T p (r : @pred AT AEQ V),
  (exists x:T, p x /\ r) =p=> ((exists x:T, p x) /\ r).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_exists_and_r:
  forall T p (r : @pred AT AEQ V),
  (exists x:T, r /\ p x) =p=> (r /\ (exists x:T, p x)).
Proof.
(* original proof tokens: 9 *)
unfold pred. pred.
apply pimpl_exists_l.
(* No more tactics to try *)
Admitted.

Lemma pimpl_and_l_exists:
  forall T p (r : @pred AT AEQ V),
  ((exists x:T, p x) /\ r) =p=> (exists x:T, p x /\ r).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_and_r_exists:
  forall T p (r : @pred AT AEQ V),
  (r /\ (exists x:T, p x)) =p=> (exists x:T, r /\ p x).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_l_and : forall (p q : @pred AT AEQ V),
  p /\ q =p=> p.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 20 *)

(* No more tactics to try *)
Admitted.

Lemma piff_comm:
  forall (a b : @pred AT AEQ V),
  (a <=p=> b) ->
  (b <=p=> a).
Proof.
(* original proof tokens: 11 *)

(* No more tactics to try *)
Admitted.

Lemma piff_refl:
  forall (a : @pred AT AEQ V),
  (a <=p=> a).
Proof.
(* original proof tokens: 11 *)

(* No more tactics to try *)
Admitted.

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
(* generated proof tokens: 12 *)

apply pimpl_refl.
Qed.

Lemma pimpl_fun_r:
  forall (p:@pred AT AEQ V),
  p =p=> (fun m => p m).
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 12 *)

apply pimpl_fun_l.
Qed.

Lemma pimpl_sep_star:
  forall (a b c d : @pred AT AEQ V),
  (a =p=> c) ->
  (b =p=> d) ->
  (a * b =p=> c * d).
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_and:
  forall (a b c d : @pred AT AEQ V),
  (a =p=> c) ->
  (b =p=> d) ->
  (a /\ b =p=> c /\ d).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_or : forall (p q p' q' : @pred AT AEQ V),
  p =p=> p'
  -> q =p=> q'
  -> p \/ q =p=> p' \/ q'.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 67 *)
unfold sep_star, lift_empty.
unfold sep_star; rewrite sep_star_is; unfold sep_star_impl.
(* No more tactics to try *)
Admitted.

Lemma sep_star_lift_r':
  forall (b: Prop) (a c: @pred AT AEQ V),
  (a =p=> [b] /\ c) ->
  (a =p=> [[b]] * c).
Proof.
(* original proof tokens: 54 *)

(* No more tactics to try *)
Admitted.

Lemma sep_star_lift_r:
  forall (a b: @pred AT AEQ V) (c: Prop),
  (a =p=> b /\ [c]) ->
  (a =p=> b * [[c]]).
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Theorem sep_star_lift_apply : forall (a : Prop) (b : @pred AT AEQ V) (m : mem),
  (b * [[a]])%pred m -> (b m /\ a).
Proof.
(* original proof tokens: 62 *)
unfold sep_star in *; simpl in *; intros; pred.
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
Proof.
(* original proof tokens: 72 *)
apply pimpl_and_dup.
(* No more tactics to try *)
Admitted.

Lemma emp_star: forall p, p <=p=> (@emp AT AEQ V) * p.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma emp_star_r: forall (F:@pred AT AEQ V),
  F =p=> (F * emp)%pred.
Proof.
(* original proof tokens: 29 *)
apply pimpl_refl.
(* No more tactics to try *)
Admitted.

Lemma piff_star_r: forall (a b c : @pred AT AEQ V),
  (a <=p=> b) ->
  (a * c <=p=> b * c).
Proof.
(* original proof tokens: 30 *)
unfold sep_star; unfold sep_star_impl.
(* No more tactics to try *)
Admitted.

Lemma piff_star_l: forall (a b c : @pred AT AEQ V),
  (a <=p=> b) ->
  (c * a <=p=> c * b).
Proof.
(* original proof tokens: 30 *)
unfold piff.
unfold piff. intros H. 

split.
unfold_sep_star.
destruct H0 as [H_impl_b b_impl_H].
(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma sep_star_lift2and:
  forall (a : @pred AT AEQ V) b,
  (a * [[b]]) =p=> a /\ [b].
Proof.
(* original proof tokens: 69 *)
unfold_sep_star.
(* No more tactics to try *)
Admitted.

Lemma sep_star_and2lift:
  forall (a : @pred AT AEQ V) b,
  (a /\ [b]) =p=> (a * [[b]]).
Proof.
(* original proof tokens: 84 *)
apply pimpl_and_dup.
(* No more tactics to try *)
Admitted.

Lemma ptsto_exact_domain : forall a v,
  exact_domain (@ptsto AT AEQ V a v).
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_ne : forall (m : @mem AT AEQ V) a a' v,
  (a |-> v)%pred m ->
  a <> a' ->
  m a' = None.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_upd_disjoint: forall V (F : @pred AT AEQ V) a v m,
  F m -> m a = None
  -> (F * a |-> v)%pred (upd m a v).
Proof.
(* original proof tokens: 154 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 177 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 63 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_value_eq : forall a v1 v2,
  v1 = v2 -> (@pimpl AT AEQ V) (a |-> v1)%pred (a |-> v2)%pred.
Proof.
(* original proof tokens: 17 *)

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
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma pimpl_or_l: forall (a b c: @pred AT AEQ V),
  (a =p=> c)
  -> (b =p=> c)
  -> (a \/ b =p=> c).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 8 *)

pred.
Qed.

Lemma pimpl_any :
  forall (p : @pred AT AEQ V),
  p =p=> any.
Proof.
(* original proof tokens: 9 *)
pred.
(* No more tactics to try *)
Admitted.

Lemma pimpl_emp_any :
  forall (p : @pred AT AEQ V),
  p =p=> emp * any.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma eq_pimpl : forall (a b : @pred AT AEQ V),
  a = b
  -> (a =p=> b).
Proof.
(* original proof tokens: 13 *)
apply piff_refl.
(* No more tactics to try *)
Admitted.

Theorem sep_star_indomain : forall (p q : @pred AT AEQ V) a,
  (p =p=> indomain a) ->
  (p * q =p=> indomain a).
Proof.
(* original proof tokens: 45 *)
unfold sep_star, impl in *; intros.
unfold_sep_star.
(* No more tactics to try *)
Admitted.

Theorem ptsto_indomain : forall (a : AT) (v : V),
  a |-> v =p=> (@indomain AT AEQ V) a.
Proof.
(* original proof tokens: 9 *)

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
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Theorem sep_star_ptsto_indomain : forall a v F (m : @mem AT AEQ V),
  (a |-> v * F)%pred m -> indomain a m.
Proof.
(* original proof tokens: 30 *)
intros a v F m H.  
pred.
(* No more tactics to try *)
Admitted.

Theorem sep_star_or_distr : forall (a b c : @pred AT AEQ V),
  (a * (b \/ c))%pred <=p=> (a * b \/ a * c)%pred.
Proof.
(* original proof tokens: 123 *)
unfold pred; pred.
unfold sep_star, sep_star_impl, pred, mem_union.
unfold sep_star.  
rewrite sep_star_is.  
unfold sep_star_impl, mem_union.  
pred.
(* No more tactics to try *)
Admitted.

Theorem sep_star_and_distr : forall (a b c : @pred AT AEQ V),
  (a * (b /\ c))%pred =p=> (a * b /\ a * c)%pred.
Proof.
(* original proof tokens: 32 *)
unfold sep_star, and, or.
unfold_sep_star.
 pred.
apply pimpl_exists_l. 
unfold pred_apply. 
pred.
(* No more tactics to try *)
Admitted.

Theorem sep_star_and_distr' : forall (a b c : @pred AT AEQ V),
  ((b /\ c) * a)%pred =p=> (b * a /\ c * a)%pred.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma sep_star_lift_empty : forall AT AEQ V P Q,
  @pimpl AT AEQ V ([[ P ]] * [[ Q ]]) ([[ P /\ Q ]]).
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Lemma lift_empty_and_distr_l : forall AT AEQ V P Q (p q : @pred AT AEQ V),
  ([[ P ]] * p) /\ ([[ Q ]] * q) =p=> [[ P /\ Q ]] * (p /\ q).
Proof.
(* original proof tokens: 87 *)
unfold_sep_star.
(* No more tactics to try *)
Admitted.

Lemma lift_empty_and_distr_r : forall AT AEQ V P Q (p q : @pred AT AEQ V),
  (p * [[ P ]]) /\ (q * [[ Q ]]) =p=> (p /\ q) * [[ P /\ Q ]].
Proof.
(* original proof tokens: 92 *)
unfold sep_star, lift_empty, and.
unfold sep_star; rewrite sep_star_is; unfold sep_star_impl.
destruct 1 as [H1 H2].
deex.
deex.
(* No more tactics to try *)
Admitted.

Theorem lift_impl : forall (P : @pred AT AEQ V) (Q : Prop), (forall m, P m -> Q) -> P =p=> [[ Q ]] * P.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_conflict : forall a (m : @mem AT AEQ V),
  ~ (a |->? * a |->?)%pred m.
Proof.
(* original proof tokens: 14 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_conflict_F : forall a F (m : @mem AT AEQ V),
  ~ (a |->? * a |->? * F)%pred m.
Proof.
(* original proof tokens: 14 *)

(* No more tactics to try *)
Admitted.

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

(* No more tactics to try *)
Admitted.

Theorem emp_complete : forall m1 m2,
  (@emp AT AEQ V) m1 -> emp m2 -> m1 = m2.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Theorem sep_star_empty_mem : forall (a b : @pred AT AEQ V),
  (a * b)%pred empty_mem -> a empty_mem /\ b empty_mem.
Proof.
(* original proof tokens: 150 *)

(* No more tactics to try *)
Admitted.

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
unfold emp, empty_mem.
(* No more tactics to try *)
Admitted.

Theorem emp_empty_mem_only : forall (m : @mem AT AEQ V),
  emp m -> m = empty_mem.
Proof.
(* original proof tokens: 20 *)

(* No more tactics to try *)
Admitted.

Theorem pred_empty_mem : forall (p : @pred AT AEQ V),
  p (@empty_mem AT AEQ V) ->
  emp =p=> p.
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Theorem emp_mem_union : forall (m1 m2 : @mem AT AEQ V),
  mem_union m1 m2 = empty_mem ->
  m1 = empty_mem /\ m2 = empty_mem.
Proof.
(* original proof tokens: 85 *)
split.
(* No more tactics to try *)
Admitted.

Theorem emp_pimpl_sep_star : forall (p q : @pred AT AEQ V),
  emp =p=> p * q ->
  (emp =p=> p) /\ (emp =p=> q).
Proof.
(* original proof tokens: 104 *)
split.
(* No more tactics to try *)
Admitted.

Theorem emp_not_ptsto : forall a v,
  ~ ((@emp AT AEQ V) =p=> a |-> v)%pred.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma mem_union_empty_mem : forall (m : @mem AT AEQ V),
  mem_union empty_mem m = m.
Proof.
(* original proof tokens: 24 *)
(* generated proof tokens: 11 *)

simpl. reflexivity.
Qed.

Lemma mem_union_empty_mem' : forall (m : @mem AT AEQ V),
  mem_union m empty_mem = m.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma mem_disjoint_empty_mem : forall (m : @mem AT AEQ V),
  mem_disjoint empty_mem m.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Theorem notindomain_empty_mem : forall a,
  notindomain a (@empty_mem AT AEQ V).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Theorem emp_notindomain : forall a (m : @mem AT AEQ V),
  emp m -> notindomain a m.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Theorem emp_pimpl_notindomain : forall a,
  emp =p=> (@notindomain AT AEQ V) a.
Proof.
(* original proof tokens: 21 *)
(* generated proof tokens: 26 *)

solve [ pred;  unfold emp, notindomain; intros; rewrite H; auto ].
Qed.

Theorem emp_mem_except : forall (m : @mem AT AEQ V) a,
  emp m -> emp (mem_except m a).
Proof.
(* original proof tokens: 25 *)
(* generated proof tokens: 53 *)

unfold emp, mem_except. intros m a H. unfold emp in H. unfold emp. intros a'. specialize (H a'). destruct (AEQ a' a); [rewrite e in H; auto |]. auto.
Qed.

Theorem mem_except_double : forall (m : @mem AT AEQ V) a,
  mem_except (mem_except m a) a = mem_except m a.
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

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

(* No more tactics to try *)
Admitted.

Theorem mem_except_ne : forall (m : @mem AT AEQ V) a a',
  a <> a' ->
  mem_except m a a' = m a'.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Theorem upd_mem_except : forall (m : @mem AT AEQ V) a v,
  upd (mem_except m a) a v = upd m a v.
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Theorem insert_mem_except : forall (m : @mem AT AEQ V) a v v0,
  m a = Some v0 ->
  insert (mem_except m a) a v = upd m a v.
Proof.
(* original proof tokens: 53 *)

(* No more tactics to try *)
Admitted.

Theorem mem_except_upd : forall (m : @mem AT AEQ V) a v,
  mem_except (upd m a v) a = mem_except m a.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma mem_except_insert: forall (m : @mem AT AEQ V) a v,
  mem_except (insert m a v) a = mem_except m a.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Theorem mem_except_none : forall (m : @mem AT AEQ V) a,
  m a = None ->
  mem_except m a = m.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma mem_except_union_comm: forall (m1 : @mem AT AEQ V) m2 a1 a2 v1,
  a1 <> a2
  -> (a1 |-> v1)%pred m1
  -> mem_except (mem_union m1 m2) a2 = mem_union m1 (mem_except m2 a2).
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Lemma mem_disjoint_mem_except : forall (m1 : @mem AT AEQ V) m2 a,
  mem_disjoint m1 m2
  -> mem_disjoint m1 (mem_except m2 a).
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Theorem notindomain_mem_union : forall a (m1 m2 : @mem AT AEQ V),
  notindomain a (mem_union m1 m2)
  <-> notindomain a m1 /\ notindomain a m2.
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Theorem notindomain_indomain_conflict : forall a (m : @mem AT AEQ V),
  notindomain a m -> indomain a m -> False.
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Theorem notindomain_mem_except : forall a a' (m : @mem AT AEQ V),
  a <> a'
  -> notindomain a (mem_except m a')
  -> notindomain a m.
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Theorem indomain_mem_except : forall a a' v (m : @mem AT AEQ V),
  a <> a'
  -> (mem_except m a') a = Some v
  -> m a = Some v.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Theorem notindomain_not_indomain : forall a (m : @mem AT AEQ V),
  notindomain a m <-> ~ indomain a m.
Proof.
(* original proof tokens: 44 *)
split.
destruct (m a) as [v|] eqn:H; simpl.
firstorder.
destruct (m a) eqn:Hm.
intuition.
destruct H0.
destruct H1.
destruct Hm.
destruct H0.
destruct H.
assert (H_indomain: ~ indomain a m).
destruct (m a) eqn: Hm.
(* No more tactics to try *)
Admitted.

Lemma indomain_upd_ne : forall (m : @mem AT AEQ V) a a' v,
  indomain a (upd m a' v)
  -> a <> a' -> indomain a m.
Proof.
(* original proof tokens: 32 *)
destruct 1 as [v' H].
(* No more tactics to try *)
Admitted.

Theorem indomain_dec : forall a (m : @mem AT AEQ V),
  {indomain a m} + {notindomain a m}.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Theorem ptsto_mem_except : forall F a v (m : @mem AT AEQ V),
  (a |-> v * F)%pred m -> F (mem_except m a).
Proof.
(* original proof tokens: 102 *)
intros F a v m.
unfold sep_star in *.
unfold_sep_star.
(* No more tactics to try *)
Admitted.

Theorem mem_except_ptsto : forall (F : @pred AT AEQ V) a v m,
  m a = Some v
  -> F (mem_except m a)
  -> (a |-> v * F)%pred m.
Proof.
(* original proof tokens: 146 *)
intros F a v m Hm Hf.
(* No more tactics to try *)
Admitted.

Theorem indomain_mem_except_indomain : forall (m : @mem AT AEQ V) a a',
  indomain a (mem_except m a') -> indomain a m.
Proof.
(* original proof tokens: 60 *)
destruct 1 as [v H].
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
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

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
unfold exact_domain in *; intros; subst.
(* No more tactics to try *)
Admitted.

Theorem septract_sep_star :
  forall (p q : @pred AT AEQ V),
  exact_domain p ->
  (p --* (p * q) =p=> q)%pred.
Proof.
(* original proof tokens: 65 *)
unfold septract, sep_star, exact_domain.
pred.
apply pimpl_exists_l.
(* No more tactics to try *)
Admitted.

Theorem septract_pimpl_l :
  forall (p p' q : @pred AT AEQ V),
  (p =p=> p') ->
  (p --* q =p=> p' --* q).
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

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
unfold exact_domain. intros p q H1 H2. unfold sep_star. unfold mem_union. unfold mem_disjoint. unfold mem_disjoint. unfold mem_disjoint in *. split; auto.
apply H2.
(* No more tactics to try *)
Admitted.

Theorem sep_star_strictly_exact : forall (p q : @pred AT AEQ V),
  strictly_exact p -> strictly_exact q ->
  strictly_exact (p * q)%pred.
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Hint Resolve mem_disjoint_assoc_1.
Hint Resolve mem_disjoint_assoc_2.
Hint Resolve mem_union_assoc.
Hint Resolve mem_disjoint_union.
Hint Resolve mem_disjoint_union_2.
Theorem sep_star_precise : forall (p q : @pred AT AEQ V),
  precise p -> precise q ->
  precise (p * q)%pred.
Proof.
(* original proof tokens: 265 *)

(* No more tactics to try *)
Admitted.

Theorem forall_strictly_exact : forall A (a : A) (p : A -> @pred AT AEQ V),
  (forall x, strictly_exact (p x)) ->
  strictly_exact (foral x, p x).
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Lemma emp_pimpl_ptsto_exfalso : forall a v,
  ~ (@emp AT AEQ V =p=> a |-> v).
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Lemma emp_pimpl_ptsto_exis_exfalso : forall a,
  ~ (@emp AT AEQ V =p=> a |->?).
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

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
split; auto.
split; auto.
(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance pimpl_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> Basics.flip Basics.impl) (@pimpl AT AEQ V).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance pimpl_pimpl_proper1 {AT AEQ V} :
  Proper (pimpl ==> Basics.flip pimpl ==> Basics.flip Basics.impl) (@pimpl AT AEQ V).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance pimpl_pimpl_proper2 {AT AEQ V} :
  Proper (Basics.flip pimpl ==> pimpl ==> Basics.impl) (@pimpl AT AEQ V).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance sep_star_apply_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> eq ==> Basics.impl) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 49 *)
unfold Proper, respectful in *; intros; unfold sep_star in *; simpl in *; intuition.
(* No more tactics to try *)
Admitted.

Instance sep_star_apply_pimpl_proper' {AT AEQ V} :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl ==> eq ==> Basics.flip Basics.impl) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Instance sep_star_apply_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> eq ==> Basics.impl) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 57 *)

(* No more tactics to try *)
Admitted.

Instance sep_star_apply_piff_proper' {AT AEQ V} :
  Proper (piff ==> piff ==> eq ==> iff) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 83 *)

(* No more tactics to try *)
Admitted.

Instance sep_star_apply_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq ==> eq) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 20 *)

unfold Proper, sep_star; intros. subst. reflexivity.
Qed.

Instance sep_star_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 45 *)

unfold Proper, respectful, sep_star. intros m1 m2 Heq1 m3 m4 Heq2. 
rewrite Heq1. rewrite Heq2. reflexivity.
Qed.

Instance sep_star_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> piff) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Instance sep_star_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 23 *)
unfold sep_star; rewrite sep_star_is; unfold sep_star_impl.
(* No more tactics to try *)
Admitted.

Instance sep_star_pimpl_proper' {AT AEQ V} :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl ==> Basics.flip pimpl) (@sep_star AT AEQ V).
Proof.
(* original proof tokens: 23 *)

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
(* generated proof tokens: 32 *)
split.
apply pimpl_and; [apply H | apply H0].
apply pimpl_and. apply H. apply H0.
Qed.

Instance and_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@and AT AEQ V).
Proof.
(* original proof tokens: 9 *)
unfold and.
unfold Proper; intros.
unfold pimpl.
(* No more tactics to try *)
Admitted.

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
(* generated proof tokens: 46 *)
intros p q Hp Hq.
unfold or.
split; intros; auto.
apply pimpl_or; [apply Hp | apply H].
apply pimpl_or; [apply Hp | apply H].
Qed.

Instance or_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@or AT AEQ V).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Example pimpl_rewrite : forall AT AEQ V a b (p : @pred AT AEQ V) q x y, p =p=> q
  -> (x /\ a * p * b \/ y =p=> x /\ a * q * b \/ y).
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Instance exists_proper_eq {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A eq ==> eq) (@exis AT AEQ V A).
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Instance exists_proper_piff {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A piff ==> piff) (@exis AT AEQ V A).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance exists_proper_pimpl {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A pimpl ==> pimpl) (@exis AT AEQ V A).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Example pimpl_exists_rewrite : forall AT AEQ V (p : @pred AT AEQ V) q, p =p=> q
  -> (exists x, p * x) =p=> (exists x, q * x).
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Instance exists_proper_pimpl_impl {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A piff ==> eq ==> iff) (@exis AT AEQ V A).
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Instance lift_empty_proper_iff {AT AEQ V} :
  Proper (iff ==> @piff _ _ _) (@lift_empty AT AEQ V).
Proof.
(* original proof tokens: 9 *)
unfold lift_empty.
unfold Proper, pointwise_relation, piff; intros; intuition.
split.
apply pimpl_and.
(* No more tactics to try *)
Admitted.

Instance lift_empty_proper_impl {AT AEQ V} :
  Proper (Basics.impl ==> @pimpl _ _ _) (@lift_empty AT AEQ V).
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 22 *)

simpl. intros P Q HPQ HP. unfold lift_empty in *. intuition.
Qed.

Instance lift_empty_proper_eq {AT AEQ V} :
  Proper (eq ==> eq) (@lift_empty AT AEQ V).
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 19 *)

unfold lift_empty; intros ???; subst. reflexivity.
Qed.

Instance lift_empty_proper_expanded_impl {AT AEQ V} :
  Proper (Basics.impl ==> eq ==> Basics.impl) (@lift_empty AT AEQ V).
Proof.
(* original proof tokens: 28 *)
unfold Basics.impl, lift_empty; intros; simpl in *; intuition.
(* No more tactics to try *)
Admitted.

Instance lift_empty_proper_expanded_flipimpl {AT AEQ V} :
  Proper (Basics.flip Basics.impl ==> eq ==> Basics.flip Basics.impl) (@lift_empty AT AEQ V).
Proof.
(* original proof tokens: 28 *)
unfold lift_empty; intros Himpl Heq m Hm; simpl in *; split; auto.
apply proj1 in H0.
(* No more tactics to try *)
Admitted.

Instance lift_empty_proper_expanded_iff {AT AEQ V} :
  Proper (iff ==> eq ==> iff) (@lift_empty AT AEQ V).
Proof.
(* original proof tokens: 27 *)
split.
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
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Instance pred_apply_pimpl_flip_proper {AT AEQ V} :
  Proper (eq ==> Basics.flip pimpl ==> Basics.flip Basics.impl) (@pred_apply AT AEQ V).
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Instance pred_apply_piff_proper {AT AEQ V} :
  Proper (eq ==> piff ==> iff) (@pred_apply AT AEQ V).
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Example pred_apply_rewrite : forall AT AEQ V p q (m : @mem AT AEQ V),
  m ## p*q -> m ## q*p.
Proof.
(* original proof tokens: 20 *)
(* generated proof tokens: 11 *)

apply sep_star_comm.
Qed.

Theorem diskIs_extract : forall AT AEQ V a v (m : @mem AT AEQ V),
  (exists F, F * a |-> v)%pred m
  -> (diskIs m =p=> diskIs (mem_except m a) * a |-> v).
Proof.
(* original proof tokens: 181 *)
unfold sep_star, diskIs, mem_except in *; pred.
rewrite sep_star_is.
(* No more tactics to try *)
Admitted.

Theorem diskIs_extract' : forall AT AEQ V a v (m : @mem AT AEQ V),
  m a = Some v
  -> (diskIs m =p=> diskIs (mem_except m a) * a |-> v).
Proof.
(* original proof tokens: 36 *)
pred.
apply diskIs_extract.
destruct H as [F ?].
(* No more tactics to try *)
Admitted.

Theorem diskIs_combine_upd : forall AT AEQ V a v (m : @mem AT AEQ V),
  diskIs (mem_except m a) * a |-> v =p=> diskIs (upd m a v).
Proof.
(* original proof tokens: 118 *)
unfold diskIs, mem_except, sep_star.
(* No more tactics to try *)
Admitted.

Theorem diskIs_combine_same : forall AT AEQ V a v (m : @mem AT AEQ V),
  (exists F, F * a |-> v)%pred m
  -> diskIs (mem_except m a) * a |-> v =p=> diskIs m.
Proof.
(* original proof tokens: 103 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 27 *)
(* generated proof tokens: 28 *)
repeat intro. unfold pred_except. intros; subst. auto.
unfold pred_except in H2; intuition.
Qed.

Instance pred_except_piff_proper {AT AEQ V} :
  Proper (piff ==> eq ==> eq ==> piff) (@pred_except AT AEQ V).
Proof.
(* original proof tokens: 27 *)
unfold pred_except; intros.

repeat (apply _; auto).
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
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Theorem pred_except_sep_star_ptsto : forall AT AEQ V (p : @pred AT AEQ V) a v a' v',
  a <> a' ->
  pred_except (p * a' |-> v') a v <=p=> pred_except p a v * a' |-> v'.
Proof.
(* original proof tokens: 449 *)
unfold pred_except.
unfold sep_star. 
pred.
unfold sep_star; rewrite sep_star_is; unfold sep_star_impl.
(* No more tactics to try *)
Admitted.

Theorem pred_except_sep_star_ptsto' : forall AT AEQ V (p : @pred AT AEQ V) a v,
  pred_except (p * a |-> v) a v =p=> p.
Proof.
(* original proof tokens: 166 *)

(* No more tactics to try *)
Admitted.

Theorem pred_except_sep_star_ptsto_notindomain : forall AT AEQ V (p : @pred AT AEQ V) a v,
  (p =p=> notindomain a) ->
  p =p=> pred_except (p * a |-> v) a v.
Proof.
(* original proof tokens: 153 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_insert_disjoint_ne: forall AT AEQ V (F : @pred AT AEQ V) a v a' v' m,
  a <> a' ->
  m a' = None ->
  (pred_except F a' v' * a |-> v)%pred m ->
  (F * a |-> v)%pred (insert m a' v').
Proof.
(* original proof tokens: 79 *)
unfold pred_except.
(* No more tactics to try *)
Admitted.

Lemma pred_except_ptsto_pimpl : forall AT AEQ V (m : @mem AT AEQ V) off v F,
  (F * off |-> v)%pred m ->
  pred_except (diskIs m) off v =p=> F.
Proof.
(* original proof tokens: 170 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_upd_bwd_or :
  forall AT AEQ V F a v v' (m : @mem AT AEQ V),
  (a |-> v' * F)%pred (upd m a v) ->
  F m \/ exists v0, (a |-> v0 * F)%pred m.
Proof.
(* original proof tokens: 87 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_insert_bwd :
  forall AT AEQ V F a v v' (m : @mem AT AEQ V),
  m a = None ->
  (a  |-> v' * F)%pred (insert m a v) ->
  F m.
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_insert_bwd_ne: forall AT AEQ V (F : @pred AT AEQ V) a v a' v' m,
  a <> a' ->
  m a' = None ->
  (F * a |-> v)%pred (insert m a' v') ->
  (pred_except F a' v' * a |-> v)%pred m.
Proof.
(* original proof tokens: 298 *)

(* No more tactics to try *)
Admitted.

Lemma sep_star_split_l: forall AT AEQ V F (x: @pred AT AEQ V) y m,
  (F * x * y)%pred m -> 
  exists F1, (F1 * x)%pred m.
Proof.
(* original proof tokens: 41 *)
unfold sep_star in *; simpl in *.
(* No more tactics to try *)
Admitted.

Lemma pimpl_sep_star_split_l: forall AT AEQ V F1 F2 (x: @pred AT AEQ V) y m,
    (F1 * x * y) %pred m ->
    (F1 * y) =p=> F2 ->
    (F1 * x) * y =p=> F2 * x.
Proof.
(* original proof tokens: 47 *)
unfold pred_apply in *; pred; repeat deex.
rewrite sep_star_comm.
unfold_sep_star.
unfold sep_star in *; unfold pred_apply in *; pred.
(* No more tactics to try *)
Admitted.

Lemma pimpl_sep_star_split_r: forall AT AEQ V F1 F2 (x: @pred AT AEQ V) y m,
    (F1 * x * y) %pred m ->
    (F1 * x) =p=> F2 ->
    (F1 * y) * x =p=> F2 * y.
Proof.
(* original proof tokens: 47 *)
unfold sep_star, sep_star_impl in *.
(* No more tactics to try *)
Admitted.

Lemma sep_star_notindomain : forall AT AEQ V (p q : @pred AT AEQ V) a,
  p =p=> notindomain a ->
  q =p=> notindomain a ->
  p * q =p=> notindomain a.
Proof.
(* original proof tokens: 47 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_notindomain : forall AT AEQ V a a' v,
  a <> a' ->
  a |-> v =p=> (@notindomain AT AEQ V) a'.
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Lemma sep_star_none : forall AT AEQ V (p q : @pred AT AEQ V) a,
  (forall m, p m -> m a = None) ->
  (forall m, q m -> m a = None) ->
  forall m, (p * q)%pred m ->
  m a = None.
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_none : forall AT AEQ V a a' v (m : @mem AT AEQ V),
  a <> a' ->
  (a |-> v)%pred m ->
  m a' = None.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Global Opaque pred.
