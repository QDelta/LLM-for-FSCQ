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
Proof.
(* skipped proof tokens: 17 *)
Admitted.
Hint Resolve KNoDup_map_elements.
Lemma mapsto_add : forall a v v' (m : Map.t V),
    Map.MapsTo a v (Map.add a v' m) -> v' = v.
Proof.
(* original proof tokens: 46 *)
(* generated proof tokens: 48 *)

intros a v v' m H.
apply MapFacts.add_mapsto_iff in H.
destruct H as [[H1 H2] | [H1 H2]]; congruence.
Qed.

Lemma map_remove_cardinal : forall (m : Map.t V) k,
    (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.remove k m) = Map.cardinal m - 1.
(* hint proof tokens: 130 *)
Proof.
    intros. destruct H as [v].
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m) (m':=m) (x:=k) (e:=v).
    lia.
    apply Map.remove_1; hnf; auto.
    intro.
    destruct (OT.eq_dec k y); unfold OT.eq in *; subst.
    - rewrite MapFacts.add_eq_o; auto.
      erewrite Map.find_1; eauto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.
Lemma map_add_cardinal : forall (m : Map.t V) k v, ~ (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal m + 1.
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Lemma map_add_dup_cardinal' : forall (m : Map.t V) k v, (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal (Map.remove k m) + 1.
Proof.
(* skipped proof tokens: 124 *)
Admitted.
Lemma map_add_dup_cardinal : forall (m : Map.t V) k v, (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal m.
(* hint proof tokens: 168 *)
Proof.
    intros.
    replace (Map.cardinal m) with ((Map.cardinal m - 1) + 1).
    erewrite <- map_remove_cardinal; eauto.
    apply map_add_dup_cardinal'; auto.
    destruct H.
    assert (Map.cardinal m <> 0); try lia.
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m).
    lia.
    apply Map.remove_1; reflexivity.
    intro.
    destruct (OT.eq_dec k y); unfold OT.eq in *; subst.
    - rewrite MapFacts.add_eq_o; auto.
      erewrite Map.find_1; eauto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.
Lemma map_elements_hd_in : forall (m : Map.t V) k w l,
    Map.elements m = (k, w) :: l ->
    Map.In k m.
Proof.
(* original proof tokens: 40 *)
(* generated proof tokens: 35 *)
intros m k w l H.
apply MapFacts.elements_in_iff.
rewrite H.
simpl.
auto.
exists w; constructor; reflexivity.
Qed.

Lemma mapeq_elements : forall m1 m2,
    @Map.Equal V m1 m2 -> Map.elements m1 = Map.elements m2.
Proof.
(* skipped proof tokens: 96 *)
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
(* skipped proof tokens: 35 *)
Admitted.
Lemma KNoDup_cons_inv : forall l k,
    KNoDup (k :: l) -> KNoDup l.
Proof.
(* skipped proof tokens: 27 *)
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
(* skipped proof tokens: 55 *)
Admitted.
Lemma is_empty_eq_map0 : forall (m : Map.t V),
    Map.is_empty m = true -> Map.Equal m map0.
(* hint proof tokens: 67 *)
Proof.
    unfold map0; intros.
    apply Map.is_empty_2 in H.
    hnf; intros.
    rewrite MapFacts.empty_o.
    apply MapFacts.not_find_in_iff.
    cbv in *; intros.
    destruct H0; eapply H; eauto.
  Qed.
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
(* skipped proof tokens: 88 *)
Admitted.
Lemma KIn_fst_In : forall a (l : list (Map.key * V)),
    KIn a l -> In (fst a) (map fst l).
Proof.
(* skipped proof tokens: 87 *)
Admitted.
Lemma In_map_fst_MapIn : forall elt k m,
    In k (map fst (Map.elements (elt:=elt) m)) <-> Map.In k m.
(* hint proof tokens: 148 *)
Proof.
    intros; split; intros.
    apply in_map_fst_exists_snd in H.
    destruct H.
    apply MapFacts.elements_in_iff.
    exists x.
    apply In_InA; auto.
    apply MapFacts.elements_in_iff in H.
    destruct H.
    apply InA_alt in H.
    destruct H; intuition.
    hnf in H0; simpl in *; intuition; subst.
    destruct x0; simpl in *; hnf in *; subst.
    generalize dependent (Map.elements m).
    induction l; intros; simpl; auto.
    inversion H1; intuition.
    destruct a; inversion H.
    tauto.
  Qed.
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
(* skipped proof tokens: 46 *)
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
(* skipped proof tokens: 31 *)
Admitted.
Lemma map_empty_find_none : forall (m : Map.t V) a,
    Map.Empty m ->
    Map.find a m = None.
(* hint proof tokens: 35 *)
Proof.
    intros.
    rewrite MapFacts.elements_o.
    apply MapProperties.elements_Empty in H.
    rewrite H; simpl; auto.
  Qed.
Lemma map_empty_not_In : forall (m : Map.t V) a,
    Map.Empty m ->
    ~ Map.In a m.
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Lemma find_none_empty : forall (m : Map.t V),
    (forall a, Map.find a m = None) ->
    Map.Empty m.
(* hint proof tokens: 31 *)
Proof.
    intros; cbv; intros.
    eapply Map.find_1 in H0.
    congruence.
  Qed.
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
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Lemma map_remove_elements_not_in : forall m a (v : V),
    ~ InA (@Map.eq_key_elt V) (a, v) (Map.elements (Map.remove a m)).
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Lemma not_in_remove_not_in : forall x y (m : Map.t V),
    ~ Map.In x m ->
    ~ Map.In x (Map.remove y m).
Proof.
(* skipped proof tokens: 75 *)
Admitted.
Lemma MapsTo_In : forall m a (v : V),
    Map.MapsTo a v m -> Map.In a m.
(* hint proof tokens: 36 *)
Proof.
    intros.
    apply MapFacts.find_mapsto_iff in H.
    apply MapFacts.in_find_iff.
    congruence.
  Qed.
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
Proof.
(* skipped proof tokens: 57 *)
Admitted.
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
(* hint proof tokens: 63 *)
Proof.
    induction ents; simpl; auto; intros.
    apply InA_cons.
    destruct (eq_key_dec a0 a); intuition.
    right; eapply IHents.
    destruct (f a); eauto.
    inversion H; subst; try congruence.
  Qed.
Lemma KNoDup_filter : forall ents f,
    KNoDup ents ->
    KNoDup (filter f ents).
(* hint proof tokens: 60 *)
Proof.
    induction ents; simpl; auto; intros.
    inversion H; subst.
    destruct (f a); intros; eauto.
    constructor.
    contradict H2.
    eapply InA_filter; eauto.
    apply IHents; eauto.
  Qed.
Lemma map_cardinal_remove_le : forall (m : Map.t V) a,
    Map.cardinal (Map.remove a m) <= Map.cardinal m.
(* hint proof tokens: 80 *)
Proof.
    intros.
    destruct (Map.find a m) eqn: Heq.
    rewrite map_remove_cardinal.
    lia.
    eexists; eapply Map.find_2; eauto.
    erewrite MapProperties.cardinal_m; eauto.
    apply map_remove_not_in_equal.
    apply MapFacts.not_find_in_iff; auto.
  Qed.
End MapUtilsFacts.
Instance map_elements_proper {V} :
    Proper (Map.Equal ==> eq) (@Map.elements V).
Proof.
(* skipped proof tokens: 26 *)
Admitted.
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
(* skipped proof tokens: 23 *)
Admitted.
Lemma subset_add_in_l: forall s v s',
    SS.In v s' ->
    SS.Subset s s' ->
    SS.Subset (SS.add v s) s'.
Proof.
(* skipped proof tokens: 50 *)
Admitted.
Lemma set_in_fold_right_add: forall x l s,
    In x l ->
    SS.In x (fold_right SS.add s l).
Proof.
(* skipped proof tokens: 40 *)
Admitted.
Lemma in_fold_right_iff: forall x l,
    InA OT.eq x l <-> SS.In x (fold_right SS.add SS.empty l).
Proof.
(* skipped proof tokens: 56 *)
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
(* hint proof tokens: 29 *)
Proof.
    induction l; cbn; intros.
    auto.
    rewrite SS.remove_spec.
    intuition auto.
  Qed.
Lemma subset_fold_add_remove_tail: forall n l s t,
    SS.Subset s (fold_right SS.add t l) ->
    SS.Subset (fold_right SS.remove s (skipn n l)) (fold_right SS.add t (firstn n l)).
Proof.
(* skipped proof tokens: 160 *)
Admitted.
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
(* hint proof tokens: 34 *)
Proof.
    intros.
    rewrite <- NoDup_NoDupA_eq.
    apply AddrSet_AVL.elements_spec2w.
    intuition.
  Qed.
Lemma elements_spec1 : forall s x,
    In x (AddrSet_AVL.elements s) <-> AddrSet_AVL.In x s.
Proof.
(* skipped proof tokens: 47 *)
Admitted.
End AddrSetFacts.
