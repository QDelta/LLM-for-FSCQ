Require Import List.
Require Import FMapFacts.
Require Import Lia.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import Arith.
Import ListNotations.
Set Implicit Arguments.
Module MapDefs (OT : UsualOrderedType) (M : S with Module E := OT).
Module Map := M.
Module MapFacts := WFacts_fun OT Map.
Module MapProperties := WProperties_fun OT Map.
Module MapOrdProperties := OrdProperties Map.
Section MapUtilsFacts.
Variable V : Type.
Definition KIn := InA (@Map.eq_key V).
Definition KNoDup := NoDupA (@Map.eq_key V).
Definition map0 := Map.empty V.
Definition map_keys (m : Map.t V) := map fst (Map.elements m).
Lemma KNoDup_map_elements : forall (m : Map.t V) ,
     KNoDup (Map.elements m).
(* hint proof tokens: 17 *)
Proof.
    intros; apply Map.elements_3w.
  Qed.
Hint Resolve KNoDup_map_elements.
Lemma mapsto_add : forall a v v' (m : Map.t V),
    Map.MapsTo a v (Map.add a v' m) -> v' = v.
(* hint proof tokens: 46 *)
Proof.
    intros.
    apply Map.find_1 in H.
    erewrite Map.find_1 in H by (apply Map.add_1; hnf; auto).
    congruence.
  Qed.
Lemma map_remove_cardinal : forall (m : Map.t V) k,
    (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.remove k m) = Map.cardinal m - 1.
Proof.
(* original proof tokens: 130 *)

(* No more tactics to try *)
Admitted.

Lemma map_add_cardinal : forall (m : Map.t V) k v, ~ (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal m + 1.
(* hint proof tokens: 39 *)
Proof.
    intros.
    erewrite MapProperties.cardinal_2 with (m:=m).
    lia.
    eauto.
    intro.
    reflexivity.
  Qed.
Lemma map_add_dup_cardinal' : forall (m : Map.t V) k v, (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal (Map.remove k m) + 1.
(* hint proof tokens: 124 *)
Proof.
    intros. destruct H.
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m).
    lia.
    apply Map.remove_1; hnf; auto.
    intro.
    destruct (OT.eq_dec k y); unfold OT.eq in *; subst.
    - rewrite MapFacts.add_eq_o; auto.
      rewrite MapFacts.add_eq_o; auto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.add_neq_o; try lia; auto.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.
Lemma map_add_dup_cardinal : forall (m : Map.t V) k v, (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal m.
Proof.
(* original proof tokens: 168 *)

(* No more tactics to try *)
Admitted.

Lemma map_elements_hd_in : forall (m : Map.t V) k w l,
    Map.elements m = (k, w) :: l ->
    Map.In k m.
(* hint proof tokens: 40 *)
Proof.
    intros.
    eexists; apply Map.elements_2.
    rewrite H.
    apply InA_cons_hd.
    constructor; hnf; eauto.
  Qed.
Lemma mapeq_elements : forall m1 m2,
    @Map.Equal V m1 m2 -> Map.elements m1 = Map.elements m2.
Proof.
(* original proof tokens: 96 *)

(* No more tactics to try *)
Admitted.

Hint Resolve MapProperties.eqke_equiv.
Lemma KNoDup_NoDup: forall (l : list (Map.key * V)),
    KNoDup l -> NoDup (map fst l).
(* hint proof tokens: 88 *)
Proof.
    induction l; simpl; intros; constructor.
    inversion H; subst.
    contradict H2.
    apply in_map_fst_exists_snd in H2; destruct H2.
    apply InA_alt.
    exists (fst a, x); intuition.
    destruct a; simpl in *.
    cbv; auto.
    inversion H; subst.
    apply IHl; auto.
  Qed.
Lemma NoDupA_cons_inv : forall T (l : list T) m a,
    NoDupA m (a :: l) -> NoDupA m l.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma KNoDup_cons_inv : forall l k,
    KNoDup (k :: l) -> KNoDup l.
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Lemma map_fst_nodup: forall (ms : Map.t V),
    NoDup (map fst (Map.elements ms)).
(* hint proof tokens: 26 *)
Proof.
    intros.
    apply KNoDup_NoDup.
    apply Map.elements_3w.
  Qed.
Lemma InA_eqke_In : forall a v l,
    InA (Map.eq_key_elt (elt:=V)) (a, v) l -> In (a, v) l.
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Lemma is_empty_eq_map0 : forall (m : Map.t V),
    Map.is_empty m = true -> Map.Equal m map0.
Proof.
(* original proof tokens: 67 *)

(* No more tactics to try *)
Admitted.

Lemma In_KIn : forall a (v : V) l,
    In a (map fst l) -> InA (@Map.eq_key V) (a, v) l.
(* hint proof tokens: 50 *)
Proof.
    intros.
    apply in_map_fst_exists_snd in H.
    destruct H.
    apply InA_alt.
    exists (a, x).
    split; auto.
    hnf; auto.
  Qed.
Lemma In_fst_KIn : forall a (l : list (Map.key * V)),
    In (fst a) (map fst l) -> KIn a l.
Proof.
(* original proof tokens: 88 *)

(* No more tactics to try *)
Admitted.

Lemma KIn_fst_In : forall a (l : list (Map.key * V)),
    KIn a l -> In (fst a) (map fst l).
Proof.
(* original proof tokens: 87 *)

(* No more tactics to try *)
Admitted.

Lemma In_map_fst_MapIn : forall elt k m,
    In k (map fst (Map.elements (elt:=elt) m)) <-> Map.In k m.
Proof.
(* original proof tokens: 148 *)

(* No more tactics to try *)
Admitted.

Lemma map_add_comm : forall A k1 k2 (v1 v2 : A) m,
    k1 <> k2 ->
    Map.Equal (Map.add k1 v1 (Map.add k2 v2 m)) (Map.add k2 v2 (Map.add k1 v1 m)).
(* hint proof tokens: 121 *)
Proof.
    intros; hnf; intro.
    destruct (OT.eq_dec y k1); destruct (OT.eq_dec y k2); subst; try congruence.
    rewrite MapFacts.add_eq_o by auto.
    rewrite MapFacts.add_neq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    setoid_rewrite MapFacts.add_eq_o at 2; auto.
    rewrite MapFacts.add_neq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    repeat rewrite MapFacts.add_neq_o; auto.
  Qed.
Lemma map_add_repeat : forall a (v v' : V) m,
    Map.Equal (Map.add a v (Map.add a v' m)) (Map.add a v m).
(* hint proof tokens: 74 *)
Proof.
    intros; hnf; intros.
    destruct (OT.eq_dec y a); subst; try congruence.
    rewrite MapFacts.add_eq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    rewrite MapFacts.add_neq_o by auto.
    repeat rewrite MapFacts.add_neq_o; auto.
  Qed.
Lemma eq_key_dec : forall (a b : Map.key * V),
    {Map.eq_key a b} + {~ Map.eq_key a b}.
(* hint proof tokens: 44 *)
Proof.
    intros; destruct a, b.
    destruct (OT.eq_dec k k0); subst.
    left; hnf; auto.
    right; hnf. tauto.
  Qed.
Lemma map_empty_find_exfalso : forall a m (v : V),
    Map.find a m = Some v ->
    Map.Empty m -> False.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma map_remove_not_in_equal : forall a (m : Map.t V),
    ~ Map.In a m ->
    Map.Equal (Map.remove a m) m.
(* hint proof tokens: 79 *)
Proof.
    intros.
    apply MapFacts.Equal_mapsto_iff; intros; split; intro.
    eapply Map.remove_3; eauto.
    apply MapFacts.remove_mapsto_iff; intuition.
    contradict H; subst.
    apply MapFacts.in_find_iff.
    apply Map.find_1 in H0.
    congruence.
  Qed.
Lemma map_remove_not_in_elements_eq : forall a (m : Map.t V),
    ~ Map.In a m ->
    Map.elements (Map.remove a m) = Map.elements m.
Proof.
(* original proof tokens: 31 *)
firstorder.
(* No more tactics to try *)
Admitted.

Lemma map_empty_find_none : forall (m : Map.t V) a,
    Map.Empty m ->
    Map.find a m = None.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma map_empty_not_In : forall (m : Map.t V) a,
    Map.Empty m ->
    ~ Map.In a m.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma find_none_empty : forall (m : Map.t V),
    (forall a, Map.find a m = None) ->
    Map.Empty m.
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Lemma map_remove_empty : forall (m : Map.t V) a,
    Map.Empty m ->
    Map.Empty (Map.remove a m).
Proof.
(* original proof tokens: 47 *)

(* No more tactics to try *)
Admitted.

Lemma not_In_not_InA : forall a v (m : Map.t V),
    ~ Map.In a m ->
    ~ InA (@Map.eq_key_elt V) (a, v) (Map.elements m).
(* hint proof tokens: 51 *)
Proof.
    intros.
    apply MapFacts.not_find_in_iff in H.
    intuition.
    eapply Map.elements_2 in H0.
    apply Map.find_1 in H0.
    congruence.
  Qed.
Lemma map_remove_elements_not_in : forall m a (v : V),
    ~ InA (@Map.eq_key_elt V) (a, v) (Map.elements (Map.remove a m)).
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Lemma not_in_remove_not_in : forall x y (m : Map.t V),
    ~ Map.In x m ->
    ~ Map.In x (Map.remove y m).
(* hint proof tokens: 75 *)
Proof.
    intros.
    destruct (OT.eq_dec x y); hnf in *; subst.
    apply Map.remove_1; hnf; auto.
    destruct (MapFacts.In_dec (Map.remove y m) x).
    contradict H.
    eapply MapFacts.remove_neq_in_iff; eauto.
    auto.
  Qed.
Lemma MapsTo_In : forall m a (v : V),
    Map.MapsTo a v m -> Map.In a m.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma In_MapsTo : forall (m : Map.t V) a,
    Map.In a m -> exists v, Map.MapsTo a v m.
(* hint proof tokens: 32 *)
Proof.
    intros.
    apply MapFacts.in_find_iff.
    apply MapFacts.in_find_iff in H; auto.
  Qed.
Lemma KIn_exists_elt_InA : forall l x,
    KIn x l ->
    exists v, InA (@Map.eq_key_elt V) (fst x, v) l.
(* hint proof tokens: 57 *)
Proof.
    intros.
    apply InA_alt in H.
    destruct H as [y [? ?]].
    destruct x, y.
    cbv in H; subst.
    exists v0; simpl.
    apply In_InA; auto.
  Qed.
Lemma length_elements_cardinal_gt : forall V (m : Map.t V) n,
    length (Map.elements m) > n ->
    Map.cardinal m > n.
(* hint proof tokens: 19 *)
Proof.
    intros; rewrite Map.cardinal_1; auto.
  Qed.
Lemma InA_filter : forall ents a f,
    InA (@Map.eq_key V) a (filter f ents) ->
    InA (@Map.eq_key V) a ents.
Proof.
(* original proof tokens: 63 *)

(* No more tactics to try *)
Admitted.

Lemma KNoDup_filter : forall ents f,
    KNoDup ents ->
    KNoDup (filter f ents).
Proof.
(* original proof tokens: 60 *)

(* No more tactics to try *)
Admitted.

Lemma map_cardinal_remove_le : forall (m : Map.t V) a,
    Map.cardinal (Map.remove a m) <= Map.cardinal m.
Proof.
(* original proof tokens: 80 *)

(* No more tactics to try *)
Admitted.

End MapUtilsFacts.
Instance map_elements_proper {V} :
    Proper (Map.Equal ==> eq) (@Map.elements V).
(* hint proof tokens: 26 *)
Proof.
    unfold Proper, respectful; intros; subst.
    apply mapeq_elements; auto.
  Qed.
End MapDefs.
Require Import FMapAVL.
Module AddrMap_AVL := FMapAVL.Make(Nat_as_OT).
Module AddrMap := MapDefs Nat_as_OT AddrMap_AVL.
Require Import MSetAVL.
Require Import MSetFacts.
Require Import Structures.OrdersEx.
Module SetDefs (OT : OrderedType) (M : S with Module E := OT).
Module SS := M.
Module SetFacts := WFacts SS.
Lemma subset_add: forall x s,
    SS.Subset s (SS.add x s).
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma subset_add_in_l: forall s v s',
    SS.In v s' ->
    SS.Subset s s' ->
    SS.Subset (SS.add v s) s'.
(* hint proof tokens: 50 *)
Proof.
    cbv [SS.Subset].
    intros.
    rewrite SS.add_spec in *.
    intuition subst; eauto.
    match goal with H: _ |- _ => rewrite H end.
    auto.
  Qed.
Lemma set_in_fold_right_add: forall x l s,
    In x l ->
    SS.In x (fold_right SS.add s l).
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma in_fold_right_iff: forall x l,
    InA OT.eq x l <-> SS.In x (fold_right SS.add SS.empty l).
Proof.
(* original proof tokens: 56 *)
cut (forall (x : OT.t) (l : list OT.t),
        InA OT.eq x l <-> SS.In x (fold_right SS.add SS.empty l)).
(* No more tactics to try *)
Admitted.

Lemma in_fold_right_remove: forall l a s,
    SS.In a (fold_right SS.remove s l) ->
    SS.In a s /\ ~InA SS.E.eq a l.
(* hint proof tokens: 66 *)
Proof.
    induction l; cbn; intros.
    intuition auto.
    inversion H0.
    rewrite SS.remove_spec in *.
    intuition subst.
    eapply IHl; eauto.
    inversion H; subst.
    congruence.
    eapply IHl; eauto.
  Qed.
Lemma in_fold_right_not_added: forall l a s,
    ~InA SS.E.eq a l -> SS.In a (fold_right SS.add s l) ->
    SS.In a s.
(* hint proof tokens: 40 *)
Proof.
    induction l; cbn; intros.
    auto.
    rewrite SS.add_spec in *.
    intuition eauto.
    contradiction H.
    eauto.
  Qed.
Lemma in_fold_right_remove_notin: forall l a s,
    ~InA SS.E.eq a l -> SS.In a s -> SS.In a (fold_right SS.remove s l).
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma subset_fold_add_remove_tail: forall n l s t,
    SS.Subset s (fold_right SS.add t l) ->
    SS.Subset (fold_right SS.remove s (skipn n l)) (fold_right SS.add t (firstn n l)).
(* hint proof tokens: 160 *)
Proof.
    cbv [SS.Subset].
    induction n, l; cbn; intros; auto.
    rewrite SS.remove_spec in *.
    intuition eauto.
    setoid_rewrite SS.add_spec in H.
    eapply in_fold_right_remove in H1.
    intuition eauto.
    eapply H in H0.
    intuition auto.
    eapply in_fold_right_not_added; eauto.
    rewrite SS.add_spec.
    eapply in_fold_right_remove in H0.
    intuition idtac.
    eapply H in H1.
    rewrite SS.add_spec in *.
    intuition auto.
    right.
    eapply IHn; eauto.
    eapply in_fold_right_remove_notin; eauto.
  Qed.
Lemma subset_inter_l: forall s t,
    SS.Subset (SS.inter s t) s.
(* hint proof tokens: 24 *)
Proof.
    cbv; intros.
    rewrite M.inter_spec in *.
    intuition.
  Qed.
Lemma subset_inter_r: forall s t,
    SS.Subset (SS.inter s t) t.
(* hint proof tokens: 24 *)
Proof.
    cbv; intros.
    rewrite M.inter_spec in *.
    intuition.
  Qed.
Lemma subset_empty: forall s,
    SS.Subset SS.empty s.
(* hint proof tokens: 26 *)
Proof.
    cbv. intros.
    rewrite SetFacts.empty_iff in *.
    intuition.
  Qed.
End SetDefs.
Module AddrSet_AVL := MSetAVL.Make (OrdersEx.Nat_as_OT).
Module AddrSet := SetDefs OrdersEx.Nat_as_OT AddrSet_AVL.
Module AddrSetFacts.
Lemma nodup_elements: forall t,
    NoDup (AddrSet_AVL.elements t).
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma elements_spec1 : forall s x,
    In x (AddrSet_AVL.elements s) <-> AddrSet_AVL.In x s.
(* hint proof tokens: 47 *)
Proof.
    intros.
    rewrite <- AddrSet_AVL.elements_spec1.
    rewrite InA_alt.
    intuition.
    eexists; eauto.
    destruct H; intuition (subst; auto).
  Qed.
End AddrSetFacts.
