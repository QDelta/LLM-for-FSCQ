Require Import Mem.
Require Import Prog.
Require Import List.
Require Import Array.
Require Import Pred.
Require Import FunctionalExtensionality.
Require Import Word.
Require Import WordAuto.
Require Import Lia.
Require Import Ring.
Require Import SepAuto.
Require Import ListUtils.
Require Import ListPred.
Import PeanoNat.
Set Implicit Arguments.
Definition list2nmem (A: Type) (l: list A) : (@mem nat Peano_dec.eq_nat_dec A) :=
  fun a => selN (map (@Some A) l) a None.
Notation "[[[ NS ':::' P ]]]" := [[ (P)%pred (list2nmem NS) ]]%pred : pred_scope.
Notation "【 NS '‣‣' P 】" := [[ (P)%pred (list2nmem NS) ]]%pred : pred_scope.
Theorem list2nmem_oob : forall A (l : list A) i,
  i >= length l
  -> (list2nmem l) i = None.
(* hint proof tokens: 30 *)
Proof.
  unfold list2nmem; intros.
  rewrite selN_oob; auto.
  rewrite map_length; auto.
Qed.
Theorem list2nmem_inbound: forall A F (l : list A) i x,
  (F * i |-> x)%pred (list2nmem l)
  -> i < length l.
(* hint proof tokens: 65 *)
Proof.
  intros.
  destruct (Compare_dec.lt_dec i (length l)); auto; exfalso.
  apply Compare_dec.not_lt in n.
  apply list2nmem_oob in n.
  apply ptsto_valid' in H.
  rewrite H in n.
  inversion n.
Qed.
Theorem list2nmem_sel: forall A F (l: list A) i x def,
  (F * i |-> x)%pred (list2nmem l)
  -> x = selN l i def.
(* hint proof tokens: 65 *)
Proof.
  intros.
  assert (i < length l).
  eapply list2nmem_inbound; eauto.
  unfold list2nmem in H.
  apply ptsto_valid' in H.
  erewrite selN_map in H by auto.
  inversion H; eauto.
Qed.
Lemma listupd_memupd: forall A l i (v : A),
  i < length l
  -> list2nmem (updN l i v) = Mem.upd (list2nmem l) i v.
(* hint proof tokens: 80 *)
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2nmem, Mem.upd.
  autorewrite with core lists.

  destruct (Peano_dec.eq_nat_dec x i).
  subst; erewrite selN_updN_eq; auto.
  rewrite map_length; auto.

  erewrite selN_updN_ne; auto.
Qed.
Theorem list2nmem_updN: forall A F (l: list A) i x y,
  (F * i |-> x)%pred (list2nmem l)
  -> (F * i |-> y)%pred (list2nmem (updN l i y)).
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_updN_selN : forall A F (l : list A) a v1 def,
  (F * a |-> v1)%pred (list2nmem (updN l a v1)) ->
  (F * a |-> selN l a def)%pred (list2nmem l).
Proof.
(* original proof tokens: 90 *)
eapply pimpl_trans.
eapply pimpl_trans.
(* No more tactics to try *)
Admitted.

Theorem listapp_memupd: forall A l (a : A),
  list2nmem (l ++ a :: nil) = Mem.upd (list2nmem l) (length l) a.
(* hint proof tokens: 195 *)
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2nmem, Mem.upd.

  destruct (Compare_dec.lt_dec x (length l)).
  - subst; rewrite selN_map with (default' := a).
    destruct (Peano_dec.eq_nat_dec x (length l)); subst.
    + rewrite selN_last; auto.
    + rewrite selN_map with (default' := a); auto.
      rewrite selN_app; auto.
    + rewrite app_length; simpl; lia.
  - destruct (Peano_dec.eq_nat_dec x (length l)).
    + subst; erewrite selN_map with (default' := a).
      rewrite selN_last; auto.
      rewrite app_length; simpl; lia.
    + repeat erewrite selN_oob with (def := None); try rewrite map_length; auto.
      lia.
      rewrite app_length; simpl; intuition.
Qed.
Theorem listapp_meminsert: forall A l (a : A),
  list2nmem (l ++ a :: nil) = Mem.insert (list2nmem l) (length l) a.
Proof.
(* original proof tokens: 225 *)
unfold list2nmem, insert; intros.
apply functional_extensionality; intro.
destruct (Peano_dec.eq_nat_dec x (length l)); subst; autorewrite with core lists; simpl; try congruence.
(* No more tactics to try *)
Admitted.

Theorem list2nmem_app: forall A (F : @pred _ _ A) l a,
  F (list2nmem l)
  -> (F * (length l) |-> a)%pred (list2nmem (l ++ a :: nil)).
Proof.
(* original proof tokens: 57 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_arrayN_app: forall A (F : @pred _ _ A) l l',
  F (list2nmem l) ->
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) (length l) l') %pred (list2nmem (l ++ l')).
(* hint proof tokens: 176 *)
Proof.
  intros.
  generalize dependent F.
  generalize dependent l.
  induction l'; intros; simpl.
  - rewrite app_nil_r.
    apply emp_star_r.
    apply H.
  - apply sep_star_assoc.
    assert (Happ := list2nmem_app F l a H).
    assert (IHla := IHl' (l ++ a :: nil) (sep_star F (ptsto (length l) a)) Happ).
    replace (length (l ++ a :: nil)) with (S (length l)) in IHla.
    replace ((l ++ a :: nil) ++ l') with (l ++ a :: l') in IHla.
    apply IHla.
    rewrite <- app_assoc; reflexivity.
    rewrite app_length; simpl.
    symmetry; apply Nat.add_1_r.
Qed.
Theorem list2nmem_removelast_is : forall A l (def : A),
  l <> nil
  -> list2nmem (removelast l) =
     fun i => if (Compare_dec.lt_dec i (length l - 1)) then Some (selN l i def) else None.
(* hint proof tokens: 100 *)
Proof.
  intros; apply functional_extensionality; intros.
  destruct (Compare_dec.lt_dec x (length l - 1)); unfold list2nmem.
  - rewrite selN_map with (default' := def).
    rewrite selN_removelast by lia; auto.
    rewrite length_removelast by auto; lia.
  - rewrite selN_oob; auto.
    rewrite map_length.
    rewrite length_removelast by auto.
    lia.
Qed.
Theorem list2nmem_removelast_list2nmem : forall A (l : list A) (def : A),
  l <> nil
  -> list2nmem (removelast l) =
     fun i => if (Peano_dec.eq_nat_dec i (length l - 1)) then None else (list2nmem l) i.
(* hint proof tokens: 119 *)
Proof.
  intros; apply functional_extensionality; intros.
  erewrite list2nmem_removelast_is with (def := def) by eauto.
  unfold list2nmem.
  destruct (Compare_dec.lt_dec x (length l - 1));
  destruct (Peano_dec.eq_nat_dec x (length l - 1)); subst; intuition.
  lia.
  erewrite selN_map with (default' := def); auto.
  lia.
  erewrite selN_oob; auto.
  rewrite map_length.
  lia.
Qed.
Lemma mem_disjoint_either: forall AT AEQ V (m1 m2 : @mem AT AEQ V) a v,
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
Theorem list2nmem_removelast: forall A F (l : list A) v,
  l <> nil
  -> (F * (length l - 1) |-> v)%pred (list2nmem l)
  -> F (list2nmem (removelast l)).
(* hint proof tokens: 140 *)
Proof.
  unfold_sep_star; unfold ptsto; intuition; repeat deex.
  assert (m1 = list2nmem (removelast l)); subst; auto.
  apply functional_extensionality; intros.
  rewrite list2nmem_removelast_list2nmem; auto.

  destruct (Peano_dec.eq_nat_dec x (length l - 1)); subst.
  apply mem_disjoint_comm in H0. 
  eapply mem_disjoint_either; eauto.

  rewrite H1; unfold mem_union.
  destruct (m1 x); subst; simpl; auto.
  apply eq_sym; apply H5; auto.
Qed.
Lemma list2nmem_except_last : forall T (l : list T) x,
  mem_except (list2nmem (l ++ x::nil)) (length l) = list2nmem l.
(* hint proof tokens: 116 *)
Proof.
  unfold mem_except, list2nmem.
  intros.
  eapply functional_extensionality; cbn; intros a.
  destruct Nat.eq_dec.
  rewrite selN_oob; auto.
  autorewrite with lists. lia.
  rewrite map_app; cbn.
  destruct (Compare_dec.lt_dec a (length l)).
  rewrite selN_app; eauto.
  autorewrite with lists; eauto.
  repeat rewrite selN_oob; auto.
  all: autorewrite with lists; cbn; lia.
Qed.
Theorem list2nmem_array: forall  A (l : list A),
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l (list2nmem l).
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array': forall  A (l l' : list A),
  l = l' ->
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l' (list2nmem l).
Proof.
(* original proof tokens: 17 *)
(* generated proof tokens: 19 *)

intros.
rewrite H.
apply list2nmem_array.
Qed.

Theorem list2nmem_arrayN_firstn_skipn: forall A (l:list A) n,
  (arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 (firstn n l) *
   arrayN (@ptsto _ Peano_dec.eq_nat_dec A) n (skipn n l))%pred (list2nmem l).
(* hint proof tokens: 126 *)
Proof.
  intros.
  case_eq (Compare_dec.lt_dec n (length l)); intros.
  - rewrite <- firstn_skipn with (l := l) (n := n) at 3.
    replace n with (length (firstn n l)) at 2.
    apply list2nmem_arrayN_app.
    apply list2nmem_array.
    apply firstn_length_l; lia.
  - rewrite firstn_oob by lia.
    rewrite skipn_oob by lia.
    eapply pimpl_apply.
    cancel.
    apply list2nmem_array.
Qed.
Lemma listpred_ptsto_list2nmem: forall T t (l : list T),
  listpred (fun a => a |->?)%pred t (list2nmem l) ->
  Permutation.Permutation t (seq 0 (length l)).
(* hint proof tokens: 271 *)
Proof.
  unfold list2nmem.
  intros.
  eapply Permutation.NoDup_Permutation.
  eapply listpred_nodup; eauto.
  decide equality.
  intuition.
  eapply ptsto_conflict; eauto.
  apply seq_NoDup.
  split; intros.
  eapply listpred_remove in H; eauto.
  destruct_lift H.
  eapply ptsto_valid in H.
  eapply in_seq.
  destruct (Compare_dec.lt_dec x (length l)); try lia.
  rewrite selN_oob in H by (autorewrite with lists; lia).
  congruence.
  intros.
  eauto using ptsto_conflict.
  destruct (In_dec Nat.eq_dec x t).
  eapply listpred_remove in H; eauto.
  eauto using ptsto_conflict.
  eapply listpred_ptsto_notindomain in H; eauto.
  cbv [notindomain list2nmem] in *.
  denote seq as Hs.
  eapply in_seq in Hs.
  erewrite selN_map in * by lia.
  congruence.
Unshelve.
  all: try exact Nat.eq_dec.
  destruct l; cbn in *; eauto; lia.
Qed.
Lemma arrayN_ptsto_linked: forall S V t l,
  arrayN (ptsto (V:=S)) 0 l =p=> listpred (fun a => exists v, a |-> v) t ->
  @listpred _ _ Nat.eq_dec V (fun a => a |->?) (seq 0 (length l)) =p=> listpred (fun a => a |->?) t.
Proof.
(* original proof tokens: 48 *)

(* No more tactics to try *)
Admitted.

Definition list2nmem_off (A: Type) (start : nat) (l: list A) : (nat -> option A) :=
  fun a => if Compare_dec.lt_dec a start then None
                             else selN (map (@Some A) l) (a - start) None.
Theorem list2nmem_off_eq : forall A (l : list A), list2nmem l = list2nmem_off 0 l.
(* hint proof tokens: 41 *)
Proof.
  unfold list2nmem, list2nmem_off; intros.
  apply functional_extensionality; intros.
  rewrite <- Minus.minus_n_O.
  reflexivity.
Qed.
Fixpoint list2nmem_fix (A : Type) (start : nat) (l : list A) : (nat -> option A) :=
  match l with
  | nil => fun a => None
  | h :: l' => fun a => if Peano_dec.eq_nat_dec a start then Some h else list2nmem_fix (S start) l' a
  end.
Lemma list2nmem_fix_below : forall (A : Type) (l : list A) start a,
  a < start -> list2nmem_fix start l a = None.
(* hint proof tokens: 39 *)
Proof.
  induction l; auto; simpl; intros.
  destruct (Peano_dec.eq_nat_dec a0 start); [lia |].
  apply IHl; lia.
Qed.
Theorem list2nmem_fix_off_eq : forall A (l : list A) n,
  list2nmem_off n l = list2nmem_fix n l.
(* hint proof tokens: 187 *)
Proof.
  induction l; intros; apply functional_extensionality; intros.
  unfold list2nmem_off; destruct (Compare_dec.lt_dec x n); auto.

  unfold list2nmem_off; simpl in *.

  destruct (Compare_dec.lt_dec x n).
  destruct (Peano_dec.eq_nat_dec x n); [lia |].
  rewrite list2nmem_fix_below by lia.
  auto.

  destruct (Peano_dec.eq_nat_dec x n).
  rewrite e; replace (n-n) with (0) by lia; auto.

  assert (x - n <> 0) by lia.
  destruct (x - n) eqn:Hxn; try congruence.

  rewrite <- IHl.
  unfold list2nmem_off.

  destruct (Compare_dec.lt_dec x (S n)); [lia |].
  f_equal; lia.
Qed.
Theorem list2nmem_fix_eq : forall A (l : list A),
  list2nmem l = list2nmem_fix 0 l.
Proof.
(* original proof tokens: 28 *)
unfold list2nmem, list2nmem_fix; intros; apply functional_extensionality; intros.
(* No more tactics to try *)
Admitted.

Theorem list2nmem_off_app_union : forall A (a b : list A) start,
  list2nmem_off start (a ++ b) = @mem_union _ Peano_dec.eq_nat_dec A (list2nmem_off start a)
                                                           (list2nmem_off (start + length a) b).
(* hint proof tokens: 115 *)
Proof.
  intros.
  repeat rewrite list2nmem_fix_off_eq.
  generalize dependent b.
  generalize dependent start.
  induction a; simpl; intros; apply functional_extensionality; intros.
  - unfold mem_union. rewrite <- plus_n_O. auto.
  - unfold mem_union in *.
    destruct (Peano_dec.eq_nat_dec x start); eauto.
    rewrite IHa.
    replace (S start + length a0) with (start + S (length a0)) by lia.
    auto.
Qed.
Theorem list2nmem_off_disjoint : forall A (a b : list A) sa sb,
  (sb >= sa + length a \/ sa >= sb + length b) ->
  @mem_disjoint _ Peano_dec.eq_nat_dec A (list2nmem_off sa a) (list2nmem_off sb b).
Proof.
(* original proof tokens: 76 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_nil_array : forall A (l : list A) start,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) start l (list2nmem nil) -> l = nil.
(* hint proof tokens: 69 *)
Proof.
  destruct l; simpl; auto.
  unfold_sep_star; unfold ptsto, list2nmem; simpl; intros.
  repeat deex.
  unfold mem_union in H0.
  apply equal_f with (start) in H0.
  rewrite H2 in H0.
  congruence.
Qed.
Lemma list2nmem_array_nil : forall A (l : list A) start,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) start nil (list2nmem_fix start l) -> l = nil.
(* hint proof tokens: 51 *)
Proof.
  destruct l; simpl; auto.
  unfold list2nmem, emp; intros.
  pose proof (H start).
  destruct (Peano_dec.eq_nat_dec start start); simpl in *; congruence.
Qed.
Theorem list2nmem_array_eq': forall A (l' l : list A) start,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) start l (list2nmem_fix start l')
  -> l' = l.
Proof.
(* original proof tokens: 276 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_eq: forall A (l' l : list A),
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l (list2nmem l')
  -> l' = l.
Proof.
(* original proof tokens: 47 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_mem_eq : forall V (l : list V) m,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec V) 0 l m ->
  m = list2nmem l.
(* hint proof tokens: 205 *)
Proof.
  intros.
  apply functional_extensionality.
  intros.
  destruct (Compare_dec.lt_dec x (length l)).
  - destruct l; [ simpl in *; lia | ].
    eapply isolateN_fwd with (i := x) in H; auto.

    assert (m x = Some (selN (v :: l) x v)).
    eapply ptsto_valid.
    pred_apply. cancel.

    assert (list2nmem (v :: l) x = Some (selN (v :: l) x v)).
    eapply ptsto_valid.
    pose proof (list2nmem_array (v :: l)).
    pred_apply. rewrite arrayN_isolate with (i := x) by auto. cancel.

    congruence.
  - eapply arrayN_oob with (i := x) in H; try lia.
    rewrite list2nmem_oob with (i := x); try lia.
    auto.
Qed.
Theorem list2nmem_array_app_eq: forall A (l l' : list A) a,
  (arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l * (length l) |-> a)%pred (list2nmem l')
  -> l' = (l ++ a :: nil).
(* hint proof tokens: 140 *)
Proof.
  intros.
  rewrite list2nmem_array_eq with (l':=l') (l:=l++a::nil); eauto.
  pred_apply.
  rewrite <- isolateN_bwd with (vs:=l++a::nil) (i:=length l) by
    ( rewrite app_length; simpl; lia ).
  rewrite firstn_app2 by auto.
  replace (S (length l)) with (length (l ++ a :: nil)) by (rewrite app_length; simpl; lia).
  rewrite skipn_oob by lia; simpl.
  instantiate (1:=a).
  rewrite selN_last by auto.
  cancel.
Qed.
Lemma list2nmem_some_bound' : forall A (m : list A) start off a,
  list2nmem_fix start m off = Some a
  -> off + 1 <= start + length m.
(* hint proof tokens: 61 *)
Proof.
  induction m; simpl; intros.
  congruence.
  destruct (Nat.eq_dec off start).
  lia.
  replace (start + S (length m)) with (S start + length m) by lia.
  eapply IHm.
  eauto.
Qed.
Lemma list2nmem_some_bound : forall A (m : list A) off a,
  list2nmem m off = Some a
  -> off + 1 <= length m.
(* hint proof tokens: 34 *)
Proof.
  intros.
  rewrite list2nmem_fix_eq in H.
  apply list2nmem_some_bound' in H.
  lia.
Qed.
Theorem list2nmem_arrayN_bound : forall A (l m : list A) off F,
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) off l)%pred (list2nmem m)
  -> l = nil \/ off + length l <= length m.
(* hint proof tokens: 82 *)
Proof.
  induction l; simpl; intros.
  intuition.
  right.
  apply sep_star_assoc in H as H'.
  apply IHl in H'.
  intuition.
  subst. simpl.
  apply sep_star_comm in H.
  apply sep_star_assoc in H.
  apply ptsto_valid in H.
  apply list2nmem_some_bound in H.
  lia.
Qed.
Theorem list2nmem_arrayN_length : forall A (l m : list A) F,
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l)%pred (list2nmem m)
  -> length l <= length m.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_ptsto_bound : forall A (l : list A) off v F,
  (F * off |-> v)%pred (list2nmem l)
  -> off < length l.
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Definition arrayN_ex A VP pts (vs : list A) i : @pred _ _ VP :=
  (arrayN pts 0 (firstn i vs) *
   arrayN pts (i + 1) (skipn (S i) vs))%pred.
Lemma arrayN_ex_one: forall V VP (pts : _ -> _ -> @pred _ _ VP) (l : list V),
    List.length l = 1 ->
    arrayN_ex pts l 0 <=p=> emp.
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_except : forall T V (vs : list T) (def : T) i (pts: _ -> _ -> @pred _ _ V),
  i < length vs
  -> arrayN pts 0 vs <=p=>
    (arrayN_ex pts vs i) * (pts i (selN vs i def)).
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_except_upd : forall V T vs (v : T) i (pts : nat -> T -> @pred _ _ V),
  i < length vs
  -> arrayN pts 0 (updN vs i v) <=p=>
    (arrayN_ex pts vs i) * (pts i v).
Proof.
(* original proof tokens: 36 *)
split.
(* No more tactics to try *)
Admitted.

Theorem arrayN_ex_updN_eq : forall T A l i (v : A) (pts : _ -> _ -> @pred _ _ T),
  arrayN_ex pts (updN l i v) i <=p=>
  arrayN_ex pts l i.
(* hint proof tokens: 34 *)
Proof.
  unfold arrayN_ex; intros; autorewrite with core lists;
  split; simpl; rewrite skipn_updN; eauto.
Qed.
Theorem arrayN_mem_upd_none : forall V vs i m (v d : V) (p : nat -> V -> pred),
  m i = None ->
  i < length vs ->
  arrayN_ex p vs i m ->
  p i (selN vs i d) (fun a => if Peano_dec.eq_nat_dec a i then Some v else None) ->
  arrayN p 0 vs (Mem.upd m i v).
Proof.
(* original proof tokens: 109 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_pick : forall V l (def : V) i,
  i < length l
  -> (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l).
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_updN : forall V ol nl (v : V) i,
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) ol i * i |-> v)%pred (list2nmem nl)
  -> i < length ol
  -> nl = updN ol i v.
(* hint proof tokens: 43 *)
Proof.
  intros.
  eapply list2nmem_array_eq; autorewrite with core lists; auto.
  pred_apply.
  rewrite isolate_fwd_upd; auto.
  cancel.
Qed.
Theorem list2nmem_array_removelast_eq : forall V (nl ol : list V),
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) ol (length ol - 1))%pred (list2nmem nl)
  -> length ol > 0
  -> nl = removelast ol.
Proof.
(* original proof tokens: 79 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_exis : forall V l (def : V) i,
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l)
  -> (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |->?)%pred (list2nmem l).
Proof.
(* original proof tokens: 13 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_ptsto_cancel : forall V i (def : V) l, i < length l ->
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l).
(* hint proof tokens: 60 *)
Proof.
  intros.
  assert (arrayN (@ptsto _ Peano_dec.eq_nat_dec V) 0 l (list2nmem l)) as Hx by eapply list2nmem_array.
  pred_apply; erewrite arrayN_except; eauto.
Qed.
Lemma list2nmem_ptsto_cancel_pair : forall A B i (def : A * B) l,
  i < length l ->
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec (A * B)) l i * 
    i |-> (fst (selN l i def), snd (selN l i def)))%pred (list2nmem l).
(* hint proof tokens: 74 *)
Proof.
  intros.
  assert (arrayN (@ptsto _ Peano_dec.eq_nat_dec (A * B)) 0 l (list2nmem l)) as Hx by eapply list2nmem_array.
  pred_apply; erewrite arrayN_except; eauto.
  rewrite <- surjective_pairing.
  cancel.
Qed.
Lemma list2nmem_sel_for_eauto : forall V A i (v v' : V) l def,
  (A * i |-> v)%pred (list2nmem l)
  -> v' = selN l i def
  -> v' = v.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_combine' : forall A VP (pts : _ -> _ -> @pred _ _ VP) (a b : list A) start,
  arrayN pts start a * arrayN pts (start + length a) b <=p=> arrayN pts start (a ++ b).
Proof.
(* original proof tokens: 73 *)
(* generated proof tokens: 25 *)

split; intros; [apply Array.arrayN_app | apply Array.arrayN_app]; auto.
Qed.

Lemma arrayN_combine : forall A VP (pts : _ -> _ -> @pred _ _ VP) (a b : list A) start off,
  off = start + length a ->
  arrayN pts start a * arrayN pts off b <=p=> arrayN pts start (a ++ b).
(* hint proof tokens: 17 *)
Proof.
  intros; subst.
  apply arrayN_combine'.
Qed.
Lemma arrayN_list2nmem : forall A (def : A) (a b : list A) F off,
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) off a)%pred (list2nmem b) ->
  a = firstn (length a) (skipn off b).
Proof.
(* original proof tokens: 77 *)
intros; unfold list2nmem; simpl.
apply list2nmem_arrayN_bound in H; auto.
(* No more tactics to try *)
Admitted.

Theorem list2nmem_ptsto_end_eq : forall A (F : @pred _ _ A) l a a',
  (F * (length l) |-> a)%pred (list2nmem (l ++ a' :: nil)) ->
  a = a'.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_arrayN_end_eq : forall A (F : @pred _ _ A) l l' l'' (def:A),
  length l' = length l'' ->
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) (length l) l')%pred (list2nmem (l ++ l'')) ->
  l' = l''.
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_off_arrayN: forall A (l : list A) off,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) off l (list2nmem_off off l).
(* hint proof tokens: 67 *)
Proof.
  intros; rewrite list2nmem_fix_off_eq.
  generalize dependent off; induction l; simpl; intros.
  - firstorder.
  - apply sep_star_comm. eapply ptsto_upd_disjoint; eauto.
    apply list2nmem_fix_below.
    lia.
Qed.
Theorem list2nmem_arrayN_app_iff : forall A (F : @pred _ _ A) l l',
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) (length l) l')%pred (list2nmem (l ++ l')) ->
  F (list2nmem l).
Proof.
(* original proof tokens: 102 *)

(* No more tactics to try *)
Admitted.

Lemma mem_except_list2nmem_oob : forall A (l : list A) a,
  a >= length l ->
  mem_except (list2nmem l) a = list2nmem l.
Proof.
(* original proof tokens: 61 *)
(* generated proof tokens: 48 *)
unfold mem_except, list2nmem; intros; apply functional_extensionality; intros.
destruct Nat.eq_dec; subst; auto.
rewrite selN_oob; auto; rewrite map_length; lia.
Qed.

Lemma list2nmem_sel_inb : forall A (l : list A) a def,
  a < length l ->
  list2nmem l a = Some (selN l a def).
(* hint proof tokens: 90 *)
Proof.
  induction l using rev_ind; intros.
  inversion H.
  rewrite listapp_memupd.

  destruct (Nat.eq_dec a (length l)); subst.
  rewrite upd_eq; auto.
  rewrite selN_last; auto.
  rewrite upd_ne; auto.
  rewrite app_length in H; simpl in H.
  erewrite IHl by lia.
  rewrite selN_app1 by lia; auto.
Qed.
Lemma sep_star_reorder_helper1 : forall AT AEQ V (a b c d : @pred AT AEQ V),
  (a * ((b * c) * d)) <=p=> (a * b * d) * c.
(* hint proof tokens: 12 *)
Proof.
  intros; split; cancel.
Qed.
Lemma list2nmem_arrayN_updN : forall V F a vl l i (v : V),
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec V) a vl)%pred (list2nmem l) ->
  i < length vl ->
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec V) a (updN vl i v))%pred (list2nmem (updN l (a + i) v)).
Proof.
(* original proof tokens: 117 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_ptsto_list2nmem_inbound : forall VT al vl (F : @pred _ _ VT) m ,
  (F * listmatch (fun a v => a |-> v) al vl)%pred (list2nmem m) ->
  Forall (fun a => a < length m) al.
Proof.
(* original proof tokens: 82 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_inj' : forall A (a b : list A) n,
  list2nmem_off n a = list2nmem_off n b ->
  a = b.
Proof.
(* original proof tokens: 206 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_inj : forall A (a b : list A),
  list2nmem a = list2nmem b ->  a = b.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Require Import PredCrash AsyncDisk.
Import ListNotations.
Lemma list2nmem_crash_xform : forall vl vsl (F : rawpred),
  possible_crash_list vsl vl ->
  F (list2nmem vsl) ->
  crash_xform F (list2nmem (synced_list vl)).
Proof.
(* original proof tokens: 495 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_list2nmem_possible_crash_list : forall vl (F : rawpred),
  crash_xform F (list2nmem vl) ->
  exists vsl, F (list2nmem vsl) /\ possible_crash_list vsl (map fst vl).
Proof.
(* original proof tokens: 498 *)
eexists.
destruct H.
(* No more tactics to try *)
Admitted.

Lemma crash_xform_list2nmem_synced : forall vl (F : rawpred),
  crash_xform F (list2nmem vl) ->
  map snd vl = repeat (@nil valu) (length vl).
Proof.
(* original proof tokens: 225 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_list2nmem_list_eq : forall F vsl vl,
  crash_xform F (list2nmem vsl) ->
  possible_crash_list vsl vl ->
  vsl = synced_list vl.
Proof.
(* original proof tokens: 151 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list2nmem_cons : forall l l' x y,
  possible_crash (list2nmem (x :: l)) (list2nmem (y :: l'))
  -> possible_crash (list2nmem l) (list2nmem l').
(* hint proof tokens: 113 *)
Proof.
  intros.
  unfold possible_crash; intros.
  destruct (Compare_dec.le_dec (length l) a);
  destruct (Compare_dec.le_dec (length l') a).
  left.
  split;
  apply list2nmem_oob; lia.

  unfold possible_crash in H;
  specialize (H (S a)); intuition.
  unfold possible_crash in H;
  specialize (H (S a)); intuition.

  unfold possible_crash in H;
  specialize (H (S a)); intuition.
Qed.
Lemma possible_crash_list2nmem_length : forall l l',
  possible_crash (list2nmem l) (list2nmem l')
  -> length l = length l'.
Proof.
(* original proof tokens: 104 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list2nmem_vssync : forall a d m,
  possible_crash (list2nmem (vssync d a)) m ->
  possible_crash (list2nmem d) m.
(* hint proof tokens: 74 *)
Proof.
  unfold vssync; intros.
  destruct (Compare_dec.lt_dec a (length d)).
  rewrite listupd_memupd in H by auto.
  eapply possible_crash_upd_nil; eauto.
  apply list2nmem_sel_inb; auto.
  rewrite updN_oob in H; auto; lia.
Qed.
Lemma possible_crash_list2nmem_vssync_vecs : forall al d m,
  possible_crash (list2nmem (vssync_vecs d al)) m ->
  possible_crash (list2nmem d) m.
(* hint proof tokens: 51 *)
Proof.
  induction al using rev_ind; simpl; auto; intros.
  rewrite vssync_vecs_app in H.
  apply IHal.
  eapply possible_crash_list2nmem_vssync; eauto.
Qed.
Lemma crash_xform_diskIs_vssync_vecs : forall al d,
  crash_xform (diskIs (list2nmem (vssync_vecs d al))) =p=>
  crash_xform (diskIs (list2nmem d)).
(* hint proof tokens: 50 *)
Proof.
  intros.
  rewrite crash_xform_diskIs; cancel.
  rewrite <- crash_xform_diskIs_r; eauto.
  eapply possible_crash_list2nmem_vssync_vecs; eauto.
Qed.
Lemma setlen_singleton : forall T l (v : T),
  setlen l 1 v = [ selN (setlen l 1 v) 0 v ].
(* hint proof tokens: 22 *)
Proof.
  unfold setlen.
  destruct l; simpl in *; congruence.
Qed.
Lemma setlen_singleton_ptsto : forall (l : list valuset),
  let l' := setlen l 1 ($0, nil) in
  (0 |-> selN l' 0 ($0, nil))%pred (list2nmem l').
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_0_list2nmem_mem_eq : forall V v (d : list V),
  (0 |-> v)%pred (list2nmem d) -> d = [v].
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_a_list2nmem_a0 : forall V v (d : list V) a,
  (a |-> v)%pred (list2nmem d) -> a = 0.
(* hint proof tokens: 87 *)
Proof.
  destruct a; eauto.
  intros; exfalso.
  unfold list2nmem, ptsto in *; intuition.
  destruct d.
  {
    simpl in *.
    congruence.
  }
  {
    assert (S a = 0 -> False) by lia.
    specialize (H1 0 H); simpl in *.
    congruence.
  }
Qed.
Lemma ptsto_a_list2nmem_mem_eq : forall V v (d : list V) a,
  (a |-> v)%pred (list2nmem d) -> d = [v].
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_pimpl : forall V m (F : @pred addr addr_eq_dec V) l,
  F m ->
  arrayN (@ptsto _ _ _) 0 l m ->
  arrayN (@ptsto _ _ _) 0 l =p=> F.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma pred_except_ptsto_pimpl : forall V (l : list V) off v F,
  (F * off |-> v)%pred (list2nmem l) ->
  pred_except (arrayN (@ptsto _ _ _) 0 l) off v =p=> F.
(* hint proof tokens: 68 *)
Proof.
  unfold pimpl; intros.
  apply pred_except_ptsto_pimpl in H.
  apply H.
  pred_apply.
  apply pred_except_pimpl_proper; auto.
  unfold pimpl; intros.
  apply list2nmem_array_mem_eq in H1; subst.
  firstorder.
Qed.
Lemma arrayN_notindomain_before : forall V (l : list V) start off,
  off < start ->
  arrayN (@ptsto _ _ V) start l =p=> notindomain off.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_notindomain_after : forall V (l : list V) start off,
  start + length l <= off ->
  arrayN (@ptsto _ _ V) start l =p=> notindomain off.
(* hint proof tokens: 50 *)
Proof.
  induction l; simpl; intros.
  apply emp_pimpl_notindomain.
  eapply sep_star_notindomain.
  eapply ptsto_notindomain; lia.
  eapply IHl; lia.
Qed.
Lemma arrayN_ex_notindomain : forall V (l : list V) off,
  arrayN_ex (@ptsto _ _ V) l off ⇨⇨ notindomain off.
(* hint proof tokens: 56 *)
Proof.
  unfold arrayN_ex; intros.
  apply sep_star_notindomain.
  apply arrayN_notindomain_after.
  rewrite firstn_length. simpl. apply Min.le_min_l.
  apply arrayN_notindomain_before.
  lia.
Qed.
Theorem arrayN_ex_pred_except : forall V (l : list V) off def,
  off < length l ->
  arrayN_ex (@ptsto _ _ _) l off =p=>
  pred_except (arrayN (@ptsto _ _ _) 0 l) off (selN l off def).
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_ex_frame_pimpl : forall V (l : list V) off v F,
  (F * off |-> v)%pred (list2nmem l) ->
  arrayN_ex (@ptsto _ _ _) l off =p=> F.
(* hint proof tokens: 74 *)
Proof.
  intros.
  eapply pimpl_trans; [ | eapply pred_except_ptsto_pimpl; eauto ].
  eapply list2nmem_sel with (def := v) in H as H'; rewrite H'.
  apply arrayN_ex_pred_except.
  eapply list2nmem_ptsto_bound; eauto.
Qed.
