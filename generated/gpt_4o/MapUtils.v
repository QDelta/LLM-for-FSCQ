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
(* generated proof tokens: 47 *)
intros a v v' m H.
apply MapFacts.add_mapsto_iff in H.
destruct H as [ [Heq Hv] | [Hneq _] ]; [ assumption | contradiction ].
Qed.

Lemma map_remove_cardinal : forall (m : Map.t V) k,
    (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.remove k m) = Map.cardinal m - 1.
Proof.
(* skipped proof tokens: 130 *)
Admitted.
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
Proof.
(* skipped proof tokens: 168 *)
Admitted.
Lemma map_elements_hd_in : forall (m : Map.t V) k w l,
    Map.elements m = (k, w) :: l ->
    Map.In k m.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma mapeq_elements : forall m1 m2,
    @Map.Equal V m1 m2 -> Map.elements m1 = Map.elements m2.
Proof.
(* skipped proof tokens: 96 *)
Admitted.
Hint Resolve MapProperties.eqke_equiv.
Lemma KNoDup_NoDup: forall (l : list (Map.key * V)),
    KNoDup l -> NoDup (map fst l).
Proof.
(* skipped proof tokens: 88 *)
Admitted.
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
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Lemma InA_eqke_In : forall a v l,
    InA (Map.eq_key_elt (elt:=V)) (a, v) l -> In (a, v) l.
Proof.
(* skipped proof tokens: 55 *)
Admitted.
Lemma is_empty_eq_map0 : forall (m : Map.t V),
    Map.is_empty m = true -> Map.Equal m map0.
Proof.
(* skipped proof tokens: 67 *)
Admitted.
Lemma In_KIn : forall a (v : V) l,
    In a (map fst l) -> InA (@Map.eq_key V) (a, v) l.
Proof.
(* skipped proof tokens: 50 *)
Admitted.
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
Proof.
(* skipped proof tokens: 148 *)
Admitted.
Lemma map_add_comm : forall A k1 k2 (v1 v2 : A) m,
    k1 <> k2 ->
    Map.Equal (Map.add k1 v1 (Map.add k2 v2 m)) (Map.add k2 v2 (Map.add k1 v1 m)).
Proof.
(* skipped proof tokens: 121 *)
Admitted.
Lemma map_add_repeat : forall a (v v' : V) m,
    Map.Equal (Map.add a v (Map.add a v' m)) (Map.add a v m).
Proof.
(* skipped proof tokens: 74 *)
Admitted.
Lemma eq_key_dec : forall (a b : Map.key * V),
    {Map.eq_key a b} + {~ Map.eq_key a b}.
Proof.
(* skipped proof tokens: 44 *)
Admitted.
Lemma map_empty_find_exfalso : forall a m (v : V),
    Map.find a m = Some v ->
    Map.Empty m -> False.
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Lemma map_remove_not_in_equal : forall a (m : Map.t V),
    ~ Map.In a m ->
    Map.Equal (Map.remove a m) m.
Proof.
(* skipped proof tokens: 79 *)
Admitted.
Lemma map_remove_not_in_elements_eq : forall a (m : Map.t V),
    ~ Map.In a m ->
    Map.elements (Map.remove a m) = Map.elements m.
Proof.
(* skipped proof tokens: 31 *)
Admitted.
Lemma map_empty_find_none : forall (m : Map.t V) a,
    Map.Empty m ->
    Map.find a m = None.
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Lemma map_empty_not_In : forall (m : Map.t V) a,
    Map.Empty m ->
    ~ Map.In a m.
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Lemma find_none_empty : forall (m : Map.t V),
    (forall a, Map.find a m = None) ->
    Map.Empty m.
Proof.
(* skipped proof tokens: 31 *)
Admitted.
Lemma map_remove_empty : forall (m : Map.t V) a,
    Map.Empty m ->
    Map.Empty (Map.remove a m).
Proof.
(* original proof tokens: 47 *)
(* generated proof tokens: 40 *)
intros m a H.
unfold Map.Empty; intros k v Hfind.
apply Map.remove_3 in Hfind; auto.
apply (H k v Hfind).
Qed.

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
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Lemma In_MapsTo : forall (m : Map.t V) a,
    Map.In a m -> exists v, Map.MapsTo a v m.
Proof.
(* skipped proof tokens: 32 *)
Admitted.
Lemma KIn_exists_elt_InA : forall l x,
    KIn x l ->
    exists v, InA (@Map.eq_key_elt V) (fst x, v) l.
Proof.
(* skipped proof tokens: 57 *)
Admitted.
Lemma length_elements_cardinal_gt : forall V (m : Map.t V) n,
    length (Map.elements m) > n ->
    Map.cardinal m > n.
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Lemma InA_filter : forall ents a f,
    InA (@Map.eq_key V) a (filter f ents) ->
    InA (@Map.eq_key V) a ents.
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Lemma KNoDup_filter : forall ents f,
    KNoDup ents ->
    KNoDup (filter f ents).
Proof.
(* skipped proof tokens: 60 *)
Admitted.
Lemma map_cardinal_remove_le : forall (m : Map.t V) a,
    Map.cardinal (Map.remove a m) <= Map.cardinal m.
Proof.
(* skipped proof tokens: 80 *)
Admitted.
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
Proof.
(* skipped proof tokens: 66 *)
Admitted.
Lemma in_fold_right_not_added: forall l a s,
    ~InA SS.E.eq a l -> SS.In a (fold_right SS.add s l) ->
    SS.In a s.
Proof.
(* skipped proof tokens: 40 *)
Admitted.
Lemma in_fold_right_remove_notin: forall l a s,
    ~InA SS.E.eq a l -> SS.In a s -> SS.In a (fold_right SS.remove s l).
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Lemma subset_fold_add_remove_tail: forall n l s t,
    SS.Subset s (fold_right SS.add t l) ->
    SS.Subset (fold_right SS.remove s (skipn n l)) (fold_right SS.add t (firstn n l)).
Proof.
(* skipped proof tokens: 160 *)
Admitted.
Lemma subset_inter_l: forall s t,
    SS.Subset (SS.inter s t) s.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma subset_inter_r: forall s t,
    SS.Subset (SS.inter s t) t.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma subset_empty: forall s,
    SS.Subset SS.empty s.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
End SetDefs.
Module AddrSet_AVL := MSetAVL.Make (OrdersEx.Nat_as_OT).
Module AddrSet := SetDefs OrdersEx.Nat_as_OT AddrSet_AVL.
Module AddrSetFacts.
Lemma nodup_elements: forall t,
    NoDup (AddrSet_AVL.elements t).
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma elements_spec1 : forall s x,
    In x (AddrSet_AVL.elements s) <-> AddrSet_AVL.In x s.
Proof.
(* skipped proof tokens: 47 *)
Admitted.
End AddrSetFacts.
