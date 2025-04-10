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
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Theorem list2nmem_inbound: forall A F (l : list A) i x,
  (F * i |-> x)%pred (list2nmem l)
  -> i < length l.
Proof.
(* skipped proof tokens: 65 *)
Admitted.
Theorem list2nmem_sel: forall A F (l: list A) i x def,
  (F * i |-> x)%pred (list2nmem l)
  -> x = selN l i def.
Proof.
(* skipped proof tokens: 65 *)
Admitted.
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
(* hint proof tokens: 55 *)
Proof.
  intros.
  rewrite listupd_memupd; auto.
  apply sep_star_comm.
  apply sep_star_comm in H.
  eapply ptsto_upd; eauto.
  eapply list2nmem_inbound; eauto.
Qed.
Lemma list2nmem_updN_selN : forall A F (l : list A) a v1 def,
  (F * a |-> v1)%pred (list2nmem (updN l a v1)) ->
  (F * a |-> selN l a def)%pred (list2nmem l).
Proof.
(* skipped proof tokens: 90 *)
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
(* hint proof tokens: 225 *)
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2nmem, Mem.insert.

  destruct (Compare_dec.lt_dec x (length l)).
  - subst; rewrite selN_map with (default' := a) by ( rewrite app_length; lia ).
    destruct (Peano_dec.eq_nat_dec x (length l)); subst.
    + rewrite selN_last; auto.
      rewrite selN_oob by ( rewrite map_length; lia ); auto.
    + rewrite selN_map with (default' := a); auto.
      rewrite selN_app; auto.
  - destruct (Peano_dec.eq_nat_dec x (length l)).
    + subst; erewrite selN_map with (default' := a) by ( rewrite app_length; simpl; lia ).
      rewrite selN_last; auto.
      rewrite selN_oob by ( rewrite map_length; lia ); auto.
    + repeat erewrite selN_oob with (def := None); try rewrite map_length; auto.
      lia.
      rewrite app_length; simpl; intuition.
Qed.
Theorem list2nmem_app: forall A (F : @pred _ _ A) l a,
  F (list2nmem l)
  -> (F * (length l) |-> a)%pred (list2nmem (l ++ a :: nil)).
(* hint proof tokens: 57 *)
Proof.
  intros.
  erewrite listapp_memupd; eauto.
  apply ptsto_upd_disjoint; auto.
  unfold list2nmem, selN.
  rewrite selN_oob; auto.
  rewrite map_length.
  lia.
Qed.
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
Proof.
(* skipped proof tokens: 100 *)
Admitted.
Theorem list2nmem_removelast_list2nmem : forall A (l : list A) (def : A),
  l <> nil
  -> list2nmem (removelast l) =
     fun i => if (Peano_dec.eq_nat_dec i (length l - 1)) then None else (list2nmem l) i.
Proof.
(* skipped proof tokens: 119 *)
Admitted.
Lemma mem_disjoint_either: forall AT AEQ V (m1 m2 : @mem AT AEQ V) a v,
  mem_disjoint m1 m2
  -> m1 a = Some v -> m2 a = None.
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Theorem list2nmem_removelast: forall A F (l : list A) v,
  l <> nil
  -> (F * (length l - 1) |-> v)%pred (list2nmem l)
  -> F (list2nmem (removelast l)).
Proof.
(* skipped proof tokens: 140 *)
Admitted.
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
(* hint proof tokens: 46 *)
Proof.
  induction l using rev_ind; intros; firstorder; simpl.
  erewrite listapp_memupd; try lia.
  eapply arrayN_app_memupd; try lia.
  eauto.
Qed.
Theorem list2nmem_array': forall  A (l l' : list A),
  l = l' ->
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l' (list2nmem l).
(* hint proof tokens: 17 *)
Proof.
  intros; subst; apply list2nmem_array.
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
Proof.
(* skipped proof tokens: 271 *)
Admitted.
Lemma arrayN_ptsto_linked: forall S V t l,
  arrayN (ptsto (V:=S)) 0 l =p=> listpred (fun a => exists v, a |-> v) t ->
  @listpred _ _ Nat.eq_dec V (fun a => a |->?) (seq 0 (length l)) =p=> listpred (fun a => a |->?) t.
Proof.
(* skipped proof tokens: 48 *)
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
Proof.
(* skipped proof tokens: 39 *)
Admitted.
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
(* hint proof tokens: 28 *)
Proof.
  intros.
  rewrite list2nmem_off_eq.
  eapply list2nmem_fix_off_eq.
Qed.
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
(* hint proof tokens: 76 *)
Proof.
  unfold mem_disjoint, list2nmem_off, not; intros; repeat deex;
    destruct (Compare_dec.lt_dec a0 sa); destruct (Compare_dec.lt_dec a0 sb); try congruence;
    apply selN_map_some_range in H0;
    apply selN_map_some_range in H2;
    lia.
Qed.
Lemma list2nmem_nil_array : forall A (l : list A) start,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) start l (list2nmem nil) -> l = nil.
Proof.
(* skipped proof tokens: 69 *)
Admitted.
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
(* hint proof tokens: 276 *)
Proof.
  induction l'; simpl; intros.
  - erewrite list2nmem_nil_array; eauto.
  - destruct l.
    + eapply list2nmem_array_nil with (start:=start).
      auto.
    + simpl in *.
      unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H.
      repeat deex.
      unfold ptsto in H1; destruct H1.
      f_equal.
      * eapply equal_f with (start) in H0 as H0'.
        unfold mem_union in H0'.
        rewrite H1 in H0'.
        destruct (Peano_dec.eq_nat_dec start start); congruence.
      * apply IHl' with (start:=S start); eauto; try lia.
        assert (m2 = list2nmem_fix (S start) l'); subst; auto.

        apply functional_extensionality; intros.
        unfold mem_union in H0.
        apply equal_f with x in H0.
        destruct (Peano_dec.eq_nat_dec x start).

        rewrite list2nmem_fix_below by lia.
        eapply mem_disjoint_either.
        eauto.
        rewrite <- e in H1.
        eauto.

        rewrite H0.
        rewrite H2; auto.
Qed.
Theorem list2nmem_array_eq: forall A (l' l : list A),
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l (list2nmem l')
  -> l' = l.
(* hint proof tokens: 47 *)
Proof.
  intros; eapply list2nmem_array_eq' with (start:=0); try rewrite <- plus_n_O; eauto.
  erewrite <- list2nmem_fix_eq; eauto.
Qed.
Theorem list2nmem_array_mem_eq : forall V (l : list V) m,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec V) 0 l m ->
  m = list2nmem l.
Proof.
(* skipped proof tokens: 205 *)
Admitted.
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
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Theorem list2nmem_arrayN_bound : forall A (l m : list A) off F,
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) off l)%pred (list2nmem m)
  -> l = nil \/ off + length l <= length m.
Proof.
(* skipped proof tokens: 82 *)
Admitted.
Theorem list2nmem_arrayN_length : forall A (l m : list A) F,
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l)%pred (list2nmem m)
  -> length l <= length m.
(* hint proof tokens: 33 *)
Proof.
  intros.
  apply list2nmem_arrayN_bound in H; destruct H; auto.
  rewrite H; simpl; lia.
Qed.
Theorem list2nmem_ptsto_bound : forall A (l : list A) off v F,
  (F * off |-> v)%pred (list2nmem l)
  -> off < length l.
(* hint proof tokens: 75 *)
Proof.
  intros.
  assert ((F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) off (v :: nil))%pred (list2nmem l)).
  pred_apply; cancel.
  apply list2nmem_arrayN_bound in H0. intuition; try congruence.
  simpl in *; lia.
Qed.
Definition arrayN_ex A VP pts (vs : list A) i : @pred _ _ VP :=
  (arrayN pts 0 (firstn i vs) *
   arrayN pts (i + 1) (skipn (S i) vs))%pred.
Lemma arrayN_ex_one: forall V VP (pts : _ -> _ -> @pred _ _ VP) (l : list V),
    List.length l = 1 ->
    arrayN_ex pts l 0 <=p=> emp.
Proof.
(* skipped proof tokens: 52 *)
Admitted.
Theorem arrayN_except : forall T V (vs : list T) (def : T) i (pts: _ -> _ -> @pred _ _ V),
  i < length vs
  -> arrayN pts 0 vs <=p=>
    (arrayN_ex pts vs i) * (pts i (selN vs i def)).
(* hint proof tokens: 40 *)
Proof.
  intros; unfold arrayN_ex.
  erewrite arrayN_isolate with (default := def); eauto.
  simpl.
  unfold piff; split; cancel.
Qed.
Theorem arrayN_except_upd : forall V T vs (v : T) i (pts : nat -> T -> @pred _ _ V),
  i < length vs
  -> arrayN pts 0 (updN vs i v) <=p=>
    (arrayN_ex pts vs i) * (pts i v).
(* hint proof tokens: 36 *)
Proof.
  intros; unfold arrayN_ex.
  erewrite isolate_fwd_upd; eauto.
  simpl.
  unfold piff; split; cancel.
Qed.
Theorem arrayN_ex_updN_eq : forall T A l i (v : A) (pts : _ -> _ -> @pred _ _ T),
  arrayN_ex pts (updN l i v) i <=p=>
  arrayN_ex pts l i.
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Theorem arrayN_mem_upd_none : forall V vs i m (v d : V) (p : nat -> V -> pred),
  m i = None ->
  i < length vs ->
  arrayN_ex p vs i m ->
  p i (selN vs i d) (fun a => if Peano_dec.eq_nat_dec a i then Some v else None) ->
  arrayN p 0 vs (Mem.upd m i v).
Proof.
(* original proof tokens: 109 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_pick : forall V l (def : V) i,
  i < length l
  -> (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l).
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Theorem list2nmem_array_updN : forall V ol nl (v : V) i,
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) ol i * i |-> v)%pred (list2nmem nl)
  -> i < length ol
  -> nl = updN ol i v.
Proof.
(* skipped proof tokens: 43 *)
Admitted.
Theorem list2nmem_array_removelast_eq : forall V (nl ol : list V),
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) ol (length ol - 1))%pred (list2nmem nl)
  -> length ol > 0
  -> nl = removelast ol.
Proof.
(* skipped proof tokens: 79 *)
Admitted.
Theorem list2nmem_array_exis : forall V l (def : V) i,
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l)
  -> (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |->?)%pred (list2nmem l).
(* hint proof tokens: 13 *)
Proof.
  intros; pred_apply; cancel.
Qed.
Lemma list2nmem_ptsto_cancel : forall V i (def : V) l, i < length l ->
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l).
Proof.
(* skipped proof tokens: 60 *)
Admitted.
Lemma list2nmem_ptsto_cancel_pair : forall A B i (def : A * B) l,
  i < length l ->
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec (A * B)) l i * 
    i |-> (fst (selN l i def), snd (selN l i def)))%pred (list2nmem l).
Proof.
(* skipped proof tokens: 74 *)
Admitted.
Lemma list2nmem_sel_for_eauto : forall V A i (v v' : V) l def,
  (A * i |-> v)%pred (list2nmem l)
  -> v' = selN l i def
  -> v' = v.
(* hint proof tokens: 29 *)
Proof.
  intros.
  apply list2nmem_sel with (def:=def) in H.
  congruence.
Qed.
Lemma arrayN_combine' : forall A VP (pts : _ -> _ -> @pred _ _ VP) (a b : list A) start,
  arrayN pts start a * arrayN pts (start + length a) b <=p=> arrayN pts start (a ++ b).
Proof.
(* original proof tokens: 73 *)
(* generated proof tokens: 21 *)

Proof.
  intros.
  rewrite arrayN_app.
  reflexivity.
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
(* hint proof tokens: 77 *)
Proof.
  induction a; simpl; intros; auto.
  rewrite skipn_selN_skipn with (def:=def).
  f_equal.
  eapply list2nmem_sel.
  pred_apply. cancel.
  eapply IHa.
  pred_apply. cancel.
  eapply list2nmem_ptsto_bound.
  pred_apply. cancel.
Qed.
Theorem list2nmem_ptsto_end_eq : forall A (F : @pred _ _ A) l a a',
  (F * (length l) |-> a)%pred (list2nmem (l ++ a' :: nil)) ->
  a = a'.
(* hint proof tokens: 34 *)
Proof.
  intros.
  apply list2nmem_sel with (def:=a) in H.
  rewrite selN_last in H; auto.
Qed.
Theorem list2nmem_arrayN_end_eq : forall A (F : @pred _ _ A) l l' l'' (def:A),
  length l' = length l'' ->
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) (length l) l')%pred (list2nmem (l ++ l'')) ->
  l' = l''.
(* hint proof tokens: 49 *)
Proof.
  intros.
  apply arrayN_list2nmem in H0.
  rewrite skipn_app in H0.
  rewrite firstn_oob in H0.
  auto.
  lia.
  exact def.
Qed.
Theorem list2nmem_off_arrayN: forall A (l : list A) off,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) off l (list2nmem_off off l).
Proof.
(* skipped proof tokens: 67 *)
Admitted.
Theorem list2nmem_arrayN_app_iff : forall A (F : @pred _ _ A) l l',
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) (length l) l')%pred (list2nmem (l ++ l')) ->
  F (list2nmem l).
Proof.
(* skipped proof tokens: 102 *)
Admitted.
Lemma mem_except_list2nmem_oob : forall A (l : list A) a,
  a >= length l ->
  mem_except (list2nmem l) a = list2nmem l.
(* hint proof tokens: 61 *)
Proof.
  unfold mem_except, list2nmem; intros.
  apply functional_extensionality; intro.
  destruct (Nat.eq_dec x a); subst; simpl; auto.
  erewrite selN_oob; auto.
  autorewrite with lists in *; lia.
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
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma list2nmem_arrayN_updN : forall V F a vl l i (v : V),
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec V) a vl)%pred (list2nmem l) ->
  i < length vl ->
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec V) a (updN vl i v))%pred (list2nmem (updN l (a + i) v)).
(* hint proof tokens: 117 *)
Proof.
  intros.
  rewrite arrayN_isolate with (i:=i) (default := v) by (rewrite length_updN; auto).
  rewrite selN_updN_eq by auto.
  rewrite firstn_updN_oob by auto.
  rewrite skipN_updN' by auto.
  apply sep_star_reorder_helper1.
  eapply list2nmem_updN with (x := selN vl i v).
  apply sep_star_reorder_helper1.
  rewrite <- arrayN_isolate; auto.
Qed.
Lemma listmatch_ptsto_list2nmem_inbound : forall VT al vl (F : @pred _ _ VT) m ,
  (F * listmatch (fun a v => a |-> v) al vl)%pred (list2nmem m) ->
  Forall (fun a => a < length m) al.
Proof.
(* skipped proof tokens: 82 *)
Admitted.
Lemma list2nmem_inj' : forall A (a b : list A) n,
  list2nmem_off n a = list2nmem_off n b ->
  a = b.
Proof.
(* skipped proof tokens: 206 *)
Admitted.
Lemma list2nmem_inj : forall A (a b : list A),
  list2nmem a = list2nmem b ->  a = b.
(* hint proof tokens: 37 *)
Proof.
  intros.
  apply list2nmem_inj' with (n := 0).
  repeat rewrite <- list2nmem_off_eq; auto.
Qed.
Require Import PredCrash AsyncDisk.
Import ListNotations.
Lemma list2nmem_crash_xform : forall vl vsl (F : rawpred),
  possible_crash_list vsl vl ->
  F (list2nmem vsl) ->
  crash_xform F (list2nmem (synced_list vl)).
(* hint proof tokens: 495 *)
Proof.
  induction vl using rev_ind; simpl; intuition.
  unfold crash_xform, possible_crash; eexists; intuition.
  setoid_rewrite length_nil in H0; auto.
  apply possible_crash_list_length in H; auto.

  unfold crash_xform, possible_crash.
  eexists; intuition. eauto.
  destruct H as [H Hx].
  destruct (Compare_dec.lt_eq_lt_dec a (length vl)).
  destruct s.
  assert (a < length vsl).
  rewrite H; autorewrite with lists; simpl; lia.

  right.
  exists (selN vsl a ($0, nil)).
  exists (selN vl a $0); intuition.
  apply selN_map; auto.
  unfold list2nmem, synced_list.
  erewrite selN_map.
  rewrite selN_combine, selN_app1, repeat_selN; auto.
  autorewrite with lists; simpl; lia.
  autorewrite with lists; auto.
  rewrite combine_length_eq; autorewrite with lists; simpl; lia.
  specialize (Hx a H1).
  rewrite selN_app1 in Hx; auto.

  right; subst.
  eexists; exists x; intuition.
  autorewrite with lists in H; simpl in H.
  unfold list2nmem; erewrite selN_map by lia; eauto.
  unfold list2nmem; rewrite synced_list_app.
  erewrite selN_map, selN_app2.
  rewrite synced_list_length, Nat.sub_diag; auto.
  rewrite synced_list_length; auto.
  rewrite app_length, synced_list_length; simpl; lia.
  rewrite app_length in H; simpl in H.
  assert (length vl < length vsl) as Hy by lia.
  specialize (Hx (length vl) Hy).
  rewrite selN_app2, Nat.sub_diag in Hx by lia; simpl in Hx.
  unfold vsmerge; eauto.

  left; split.
  rewrite app_length in H; simpl in H.
  unfold list2nmem; erewrite selN_oob; auto.
  rewrite map_length; lia.
  unfold list2nmem; erewrite selN_oob; auto.
  rewrite map_length, synced_list_length, app_length; simpl; lia.
  Unshelve. all: eauto.
Qed.
Lemma crash_xform_list2nmem_possible_crash_list : forall vl (F : rawpred),
  crash_xform F (list2nmem vl) ->
  exists vsl, F (list2nmem vsl) /\ possible_crash_list vsl (map fst vl).
Proof.
(* skipped proof tokens: 498 *)
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
(* hint proof tokens: 151 *)
Proof.
  intros.
  destruct H0 as [Heq Hx].
  apply crash_xform_list2nmem_synced in H.
  apply list_selN_ext with (default := ($0, nil)); intros.
  rewrite synced_list_length; auto.
  rewrite synced_list_selN.
  specialize (Hx _ H0); unfold vsmerge in Hx.
  rewrite surjective_pairing at 1.
  erewrite <- selN_map with (f := snd) in * by auto.
  rewrite H in *.
  rewrite repeat_selN in * by auto.
  simpl in *; intuition.
  rewrite <- H1; simpl; auto.
  Unshelve. all: eauto.
Qed.
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
(* skipped proof tokens: 104 *)
Admitted.
Lemma possible_crash_list2nmem_vssync : forall a d m,
  possible_crash (list2nmem (vssync d a)) m ->
  possible_crash (list2nmem d) m.
Proof.
(* skipped proof tokens: 74 *)
Admitted.
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
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Lemma setlen_singleton_ptsto : forall (l : list valuset),
  let l' := setlen l 1 ($0, nil) in
  (0 |-> selN l' 0 ($0, nil))%pred (list2nmem l').
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma ptsto_0_list2nmem_mem_eq : forall V v (d : list V),
  (0 |-> v)%pred (list2nmem d) -> d = [v].
Proof.
(* skipped proof tokens: 50 *)
Admitted.
Lemma ptsto_a_list2nmem_a0 : forall V v (d : list V) a,
  (a |-> v)%pred (list2nmem d) -> a = 0.
Proof.
(* original proof tokens: 87 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_a_list2nmem_mem_eq : forall V v (d : list V) a,
  (a |-> v)%pred (list2nmem d) -> d = [v].
(* hint proof tokens: 44 *)
Proof.
  intros.
  eapply ptsto_a_list2nmem_a0 in H as H'; subst.
  eapply ptsto_0_list2nmem_mem_eq; eauto.
Qed.
Theorem arrayN_pimpl : forall V m (F : @pred addr addr_eq_dec V) l,
  F m ->
  arrayN (@ptsto _ _ _) 0 l m ->
  arrayN (@ptsto _ _ _) 0 l =p=> F.
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma pred_except_ptsto_pimpl : forall V (l : list V) off v F,
  (F * off |-> v)%pred (list2nmem l) ->
  pred_except (arrayN (@ptsto _ _ _) 0 l) off v =p=> F.
Proof.
(* skipped proof tokens: 68 *)
Admitted.
Lemma arrayN_notindomain_before : forall V (l : list V) start off,
  off < start ->
  arrayN (@ptsto _ _ V) start l =p=> notindomain off.
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Lemma arrayN_notindomain_after : forall V (l : list V) start off,
  start + length l <= off ->
  arrayN (@ptsto _ _ V) start l =p=> notindomain off.
Proof.
(* skipped proof tokens: 50 *)
Admitted.
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
(* skipped proof tokens: 46 *)
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
