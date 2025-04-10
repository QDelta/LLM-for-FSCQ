Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import List.
Require Import ListUtils.
Require Import Word.
Import ListNotations.
Set Implicit Arguments.
Section ListRevSel.
Variable T : Type.
Variable l : (list T).
Definition selR n def :=
    if lt_dec n (length l) then selN l (length l - n - 1) def else def.
Lemma selR_oob : forall n def,
    n >= length l -> selR n def = def.
(* hint proof tokens: 29 *)
Proof.
    unfold selR; intros.
    destruct (lt_dec n (length l)); try lia; auto.
  Qed.
Lemma selR_inb : forall n def,
    n < length l -> selR n def = selN l (length l - n - 1) def.
Proof.
(* original proof tokens: 30 *)
(* generated proof tokens: 34 *)

unfold selR. intros. 
destruct (lt_dec n (length l)); [| lia]. 
reflexivity. 
Qed.

End ListRevSel.
Section NonEmptyList.
Variable T : Type.
Definition nelist  := (T * list T)%type.
Definition singular x : nelist := (x, nil).
Definition latest (ds : nelist) := hd (fst ds) (snd ds).
Definition latest_cons : forall d0 d ds, latest (d0, d :: ds) = d.
Proof.
(* original proof tokens: 11 *)
(* generated proof tokens: 14 *)

intros. simpl. reflexivity.
Qed.

Definition nthd n (ds : nelist) := selN (snd ds) (length (snd ds) - n) (fst ds).
Lemma nthd_0 : forall ds, nthd 0 ds = fst ds.
(* hint proof tokens: 24 *)
Proof.
    unfold nthd; intros; rewrite selN_oob; auto; lia.
  Qed.
Lemma nthd_oob : forall ds n, n >= length (snd ds) -> nthd n ds = latest ds.
(* hint proof tokens: 44 *)
Proof.
    unfold nthd, latest; intros; destruct ds; simpl in *.
    replace (length l - n) with 0 by lia.
    destruct l; firstorder.
  Qed.
Definition pushd (d : T) (ds : nelist) : nelist :=
      (fst ds, d :: snd ds).
Theorem latest_pushd : forall d ds,
    latest (pushd d ds) = d.
(* hint proof tokens: 18 *)
Proof.
    unfold pushd; intros; apply latest_cons.
  Qed.
Fixpoint pushdlist (dlist : list T) (ds : nelist) : nelist :=
      match dlist with
      | nil => ds
      | d :: dlist' => pushdlist dlist' (pushd d ds)
      end.
Definition popn (n : nat) (ds : nelist) : nelist :=
      (nthd n ds, cuttail n (snd ds)).
Lemma popn_0 : forall ds,
    popn 0 ds = ds.
(* hint proof tokens: 35 *)
Proof.
    unfold popn; intros.
    rewrite nthd_0, cuttail_0.
    rewrite surjective_pairing; auto.
  Qed.
Lemma popn_oob : forall ds n,
    n >= length (snd ds) -> popn n ds = (latest ds, nil).
Proof.
(* original proof tokens: 34 *)
(* generated proof tokens: 29 *)
simpl. unfold popn. intros. rewrite nthd_oob; auto.
rewrite cuttail_oob; auto.
Qed.

Lemma singular_latest : forall ds, snd ds = nil -> latest ds = fst ds.
(* hint proof tokens: 23 *)
Proof.
    unfold latest; destruct ds, l; simpl; intuition; inversion H.
  Qed.
Lemma singular_nthd : forall ds n, snd ds = nil -> nthd n ds = fst ds.
(* hint proof tokens: 23 *)
Proof.
    unfold latest; destruct ds, l; simpl; intuition; inversion H.
  Qed.
Lemma popn_oob_singular' : forall ds n,
    n >= length (snd ds) -> snd (popn n ds) = nil.
(* hint proof tokens: 25 *)
Proof.
    unfold popn; intros.
    rewrite cuttail_oob by lia; auto.
  Qed.
Lemma popn_oob_singular : forall ds n,
    n >= length (snd ds) -> popn n ds = singular (latest ds).
(* hint proof tokens: 34 *)
Proof.
    unfold popn, singular; intros.
    rewrite cuttail_oob by lia.
    rewrite nthd_oob; auto.
  Qed.
Lemma popn_popn : forall ds m n,
    popn m (popn n ds) = popn (n + m) ds.
(* hint proof tokens: 178 *)
Proof.
    unfold popn; intros; simpl.
    rewrite cuttail_cuttail; f_equal.
    unfold nthd; simpl.
    rewrite cuttail_length.
    destruct (le_dec n (length (snd ds))).
    replace (length (snd ds) - (n + m)) with (length (snd ds) - n - m) by lia.
    unfold cuttail.
    destruct (lt_dec (length (snd ds) - n - m) (length (snd ds) - n)).
    rewrite selN_firstn at 1; auto.
    apply selN_inb; lia.
    rewrite selN_oob.
    f_equal; lia.
    rewrite firstn_length; apply Nat.min_case_strong; lia.
    rewrite cuttail_oob by lia.
    simpl; f_equal; lia.
  Qed.
Lemma popn_tail : forall n d0 d ds,
    popn (S n) (d0, ds ++ [d]) = popn n (d, ds).
Proof.
(* original proof tokens: 102 *)

(* No more tactics to try *)
Admitted.

Lemma pushdlist_app : forall d l' l,
    pushdlist l' (d, l) = (d, (rev l') ++ l)%list.
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma nthd_popn : forall m n ds,
    nthd n (popn m ds) = nthd (m + n) ds.
Proof.
(* original proof tokens: 152 *)

(* No more tactics to try *)
Admitted.

Definition d_in d (l : nelist) := d = fst l \/ In d (snd l).
Theorem d_in_pushdlist : forall dlist ds d,
    d_in d (pushdlist dlist ds) ->
    In d dlist \/ d_in d ds.
(* hint proof tokens: 64 *)
Proof.
    induction dlist; simpl; intros; auto.
    edestruct (IHdlist _ _ H).
    intuition.
    destruct ds.
    inversion H0; simpl in *.
    right. left. eauto.
    intuition.
    right. right. eauto.
  Qed.
Theorem d_in_app : forall d a l1 l2,
    d_in d (a, (l1 ++ l2)) ->
    In d l1 \/ d_in d (a, l2).
Proof.
(* original proof tokens: 67 *)

(* No more tactics to try *)
Admitted.

Theorem nthd_in_ds : forall ds n,
    d_in (nthd n ds) ds.
Proof.
(* original proof tokens: 64 *)

(* No more tactics to try *)
Admitted.

Theorem latest_in_ds : forall ds,
    d_in (latest ds) ds.
(* hint proof tokens: 28 *)
Proof.
    unfold d_in, latest.
    destruct ds; simpl.
    destruct l; simpl; intuition.
  Qed.
Theorem d_in_In : forall d d' l,
    d_in d (d', l) -> In d (d' :: l).
(* hint proof tokens: 16 *)
Proof.
    unfold d_in; simpl; intuition.
  Qed.
Theorem d_in_In' : forall d d' l,
    In d (d' :: l) -> d_in d (d', l).
Proof.
(* original proof tokens: 16 *)
(* generated proof tokens: 17 *)

unfold d_in; simpl; intros; intuition.
Qed.

Lemma d_in_pushd : forall ds d d',
    d_in d (pushd d' ds) ->
    d = d' \/ d_in d ds.
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Lemma d_in_nthd: forall l d,
    d_in d l ->
    exists n, d = nthd n l.
(* hint proof tokens: 101 *)
Proof.
    induction 1.
    - exists 0.
      erewrite nthd_0; eauto.
    - eapply in_selN_exists in H as H'.
      destruct H'.
      unfold nthd.
      exists (Datatypes.length (snd l)-x).
      replace (Datatypes.length (snd l) - (Datatypes.length (snd l) - x)) with x by lia.
      intuition.
      rewrite H2; eauto.
  Qed.
Lemma latest_nthd: forall l,
    latest l = nthd (Datatypes.length (snd l)) l.
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Lemma pushd_latest: forall l d,
    latest (pushd d l)  = d.
Proof.
(* original proof tokens: 23 *)
(* generated proof tokens: 22 *)

intros.
unfold pushd, latest.
simpl.
reflexivity.
Qed.

Lemma length_popn : forall n ds,
    length (snd (popn n ds)) = length (snd ds) - n.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma latest_popn : forall n ds,
    latest (popn n ds) = latest ds.
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Inductive NEListSubset : nelist -> nelist -> Prop :=
  | NESubsetNil : forall d, NEListSubset (d, nil) (d, nil)
  | NESubsetHead : forall ds d',
      NEListSubset (pushd d' ds) (d', nil)
  | NESubsetIn : forall ds ds' d,
      NEListSubset ds ds'
      -> NEListSubset (pushd d ds) (pushd d ds')
  | NESubsetNotIn : forall ds ds' d,
      NEListSubset ds ds'
      -> NEListSubset (pushd d ds) ds'.
Inductive ListSubset (T : Type) : list T -> list T -> Prop :=
  | SubsetNil : ListSubset nil nil
  | SubsetIn : forall l1 l2 a, ListSubset l1 l2 -> ListSubset (a :: l1) (a :: l2)
  | SubsetNotIn : forall l1 l2 a, ListSubset l1 l2 -> ListSubset (a :: l1) l2.
Hint Constructors ListSubset.
Lemma list_subset_nil : forall T (l : list T),
    ListSubset l nil.
Proof.
(* original proof tokens: 14 *)
induction l; constructor.
(* No more tactics to try *)
Admitted.

Lemma nelist_list_subset : forall ds ds',
    NEListSubset ds ds' <-> ListSubset (snd ds ++ [fst ds]) (snd ds' ++ [fst ds']).
Proof.
(* original proof tokens: 473 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_equal : forall ds,
    NEListSubset ds ds.
(* hint proof tokens: 33 *)
Proof.
    destruct ds.
    induction l.
    constructor.
    eapply NESubsetIn in IHl.
    eauto.
  Qed.
Lemma nelist_subset_oldest : forall l t,
    NEListSubset (t, l) (t, nil).
(* hint proof tokens: 43 *)
Proof.
    induction l; intros; simpl.
    constructor.

    replace t with (fst (t, l)) at 1 by auto.
    econstructor.
    eauto.
  Qed.
Lemma nelist_subset_latest : forall ds,
    NEListSubset ds (latest ds, nil).
(* hint proof tokens: 51 *)
Proof.
    unfold latest.
    destruct ds, l; simpl.
    constructor.
    replace (_, _) with (pushd t0 (t, l)) by auto.
    eapply NESubsetHead; eauto.
  Qed.
Lemma nelist_subset_oldest_latest' : forall l t,
    length l > 0
    -> NEListSubset (t, l) (t, hd t l :: nil).
(* hint proof tokens: 103 *)
Proof.
    destruct l; intros; simpl.
    inversion H.

    replace t0 with (fst (t0, l)) at 1 by auto.
    replace t0 with (fst (t0, @nil T)) at 2 by auto.
    replace l with (snd (t0, l)) by auto.
    replace nil with (snd (t0, @nil T)) by auto.
    econstructor.
    apply nelist_subset_oldest.
  Qed.
Lemma nelist_subset_oldest_latest : forall ds,
    length (snd ds) > 0
    -> NEListSubset ds (fst ds, latest ds :: nil).
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_popn1 : forall ds ds',
    NEListSubset (popn 1 ds) ds' ->
    NEListSubset ds ds'.
Proof.
(* original proof tokens: 386 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_popn : forall n ds ds',
    NEListSubset (popn n ds) ds' ->
    NEListSubset ds ds'.
(* hint proof tokens: 73 *)
Proof.
    induction n; simpl; intros.
    rewrite popn_0 in H; auto.
    replace (S n) with (1 + n) in H by lia.
    rewrite <- popn_popn in H.
    apply IHn in H.
    eapply nelist_subset_popn1; eauto.
  Qed.
Lemma nelist_subset_nthd_latest : forall n ds,
    n < length (snd ds) ->
    NEListSubset ds (nthd n ds, latest ds :: nil).
(* hint proof tokens: 89 *)
Proof.
    induction n; simpl; intros.
    rewrite nthd_0.
    apply nelist_subset_oldest_latest; auto.
    replace (S n) with (1 + n) by lia.
    rewrite <- nthd_popn.
    erewrite <- latest_popn.
    eapply nelist_subset_popn.
    apply IHn; simpl.
    rewrite cuttail_length.
    lia.
  Qed.
Lemma nelist_subset_popn1' : forall ds ds',
    NEListSubset ds ds' ->
    NEListSubset ds (popn 1 ds').
Proof.
(* original proof tokens: 326 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_popn' : forall n ds ds',
    NEListSubset ds ds' ->
    NEListSubset ds (popn n ds').
(* hint proof tokens: 65 *)
Proof.
    induction n; simpl; intros.
    rewrite popn_0; auto.
    replace (S n) with (1 + n) by lia.
    rewrite <- popn_popn.
    apply IHn.
    eapply nelist_subset_popn1'; eauto.
  Qed.
Lemma pushd_length : forall ds d,
    length (snd (pushd d ds)) = S (length (snd ds)).
Proof.
(* original proof tokens: 18 *)
(* generated proof tokens: 24 *)

intro ds; induction ds as [d0 l]; simpl; intros; reflexivity.
Qed.

Lemma pushdlist_length: forall dlist ds,
    length (snd (pushdlist dlist ds)) =
    length dlist + length (snd ds).
Proof.
(* original proof tokens: 37 *)
simpl. induction dlist; destruct ds; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma nthd_pushd : forall l t n d,
    n <= length l
    -> nthd n (pushd d (t, l)) = nthd n (t, l).
Proof.
(* original proof tokens: 81 *)

(* No more tactics to try *)
Admitted.

Lemma nthd_pushd' : forall ds n d,
    n <= length (snd ds)
    -> nthd n (pushd d ds) = nthd n ds.
(* hint proof tokens: 22 *)
Proof.
    destruct ds; intros.
    apply nthd_pushd; auto.
  Qed.
Lemma nthd_pushd_latest : forall l t d n,
    n = S (length l)
    -> nthd n (pushd d (t, l)) = d.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma nthd_pushd_latest' : forall ds d n,
    n = S (length (snd ds))
    -> nthd n (pushd d ds) = d.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma popn_pushd_comm : forall d ds n,
    n <= length (snd ds) ->
    popn n (pushd d ds) = pushd d (popn n ds).
(* hint proof tokens: 34 *)
Proof.
    unfold popn; simpl; intros.
    rewrite nthd_pushd' by auto.
    rewrite cuttail_cons; auto.
  Qed.
Lemma nelist_subset_nthd : forall ds ds',
    NEListSubset ds ds'
    -> forall n' d,
        n' <= length (snd ds')
        -> nthd n' ds' = d
        -> exists n, n <= length (snd ds) /\ nthd n ds = d.
(* hint proof tokens: 260 *)
Proof.
    induction 1; intros; simpl.

    exists 0.
    rewrite nthd_0; eauto.

    simpl in *.
    inversion H0; subst.
    exists (S (length (snd ds))); intuition.
    setoid_rewrite nthd_pushd_latest; eauto.

    destruct (lt_dec n' (length (snd (pushd d ds'))));
    destruct ds, ds'.
    rewrite nthd_pushd in H1.
    apply IHNEListSubset in H1.
    inversion H1.
    exists x; intuition.
    rewrite nthd_pushd; auto.
    rewrite pushd_length in l; lia.
    rewrite pushd_length in l; simpl in *; lia.

    rewrite nthd_pushd_latest in H1; subst.
    exists (S (length l)); intuition.
    rewrite nthd_pushd_latest; auto.
    replace l0 with (snd (t0, l0)) by auto.
    rewrite <- pushd_length with (d:=d).
    lia.

    apply IHNEListSubset in H1; auto.
    inversion H1.
    intuition.
    exists x; intuition.
    setoid_rewrite nthd_pushd; auto.
  Qed.
End NonEmptyList.
Notation " ds '!!'" := (latest ds) (at level 1).
Definition d_map A B (f : A -> B) (ds : nelist A) :=
  (f (fst ds), map f (snd ds)).
Lemma d_map_latest : forall A B (f : A -> B) ds,
  latest (d_map f ds) = f (latest ds).
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma d_map_fst : forall A B (f : A -> B) ds,
  fst (d_map f ds) = f (fst ds).
Proof.
(* original proof tokens: 14 *)
(* generated proof tokens: 20 *)

intros; unfold d_map; destruct ds; simpl; auto.
Qed.

Lemma d_map_nthd : forall A B (f : A -> B) ds n,
  nthd n (d_map f ds) = f (nthd n ds).
(* hint proof tokens: 98 *)
Proof.
  unfold d_map; intros; simpl.
  destruct n.
  repeat rewrite nthd_0; auto.
  unfold nthd; destruct (lt_dec n (length (snd ds))); simpl.
  erewrite selN_map, map_length; auto.
  rewrite map_length; lia.
  rewrite map_length.
  replace (length (snd ds) - S n) with 0 by lia.
  destruct ds, l; simpl; auto.
Qed.
Lemma d_in_d_map : forall A B ds (f : A -> B) d,
  d_in d (d_map f ds) ->
  exists d', d_in d' ds /\ d = f d'.
Proof.
(* original proof tokens: 80 *)

(* No more tactics to try *)
Admitted.

Lemma dmap_popn_comm : forall A B n f (ds : nelist A),
  @popn B n (d_map f ds) = d_map f (popn n ds).
Proof.
(* original proof tokens: 88 *)

(* No more tactics to try *)
Admitted.

Definition NEforall T (p : T -> Prop) (l : nelist T) :=
  p (fst l) /\ Forall p (snd l).
Definition NEforall2 T1 T2 (p : T1 -> T2 -> Prop) (l1 : nelist T1) (l2 : nelist T2) :=
  p (fst l1) (fst l2) /\ Forall2 p (snd l1) (snd l2).
Theorem NEforall2_pushd : forall T1 T2 (p : T1 -> T2 -> _) l1 l2 e1 e2,
  NEforall2 p l1 l2 ->
  p e1 e2 ->
  NEforall2 p (pushd e1 l1) (pushd e2 l2).
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Theorem NEforall_impl : forall T (p1 p2 : T -> Prop) l,
  NEforall p1 l ->
  (forall a, p1 a -> p2 a) ->
  NEforall p2 l.
(* hint proof tokens: 25 *)
Proof.
  destruct l; unfold NEforall; intuition.
  eapply Forall_impl; eauto.
Qed.
Theorem NEforall2_impl : forall T1 T2 (p1 p2 : T1 -> T2 -> Prop) l1 l2,
  NEforall2 p1 l1 l2 ->
  (forall a b, p1 a b -> p2 a b) ->
  NEforall2 p2 l1 l2.
(* hint proof tokens: 80 *)
Proof.
  destruct l1; destruct l2; unfold NEforall2; intuition; simpl in *.
  apply forall2_forall in H2 as H2'.
  apply forall2_length in H2 as H2''.
  apply forall_forall2; eauto.
  eapply Forall_impl; eauto.
  intros; destruct a; eauto.
Qed.
Theorem NEforall2_exists : forall T1 T2 (p p' : T1 -> T2 -> Prop) (f2 : T2 -> T2) l1 l2,
  NEforall2 p l1 l2 ->
  (forall e1 e2, p e1 e2 -> exists e1', p' e1' (f2 e2)) ->
  exists l1',
  NEforall2 p' l1' (d_map f2 l2).
(* hint proof tokens: 120 *)
Proof.
  unfold NEforall2.
  destruct l1, l2; simpl in *; intros.
  generalize dependent l0.
  induction l; intuition.
  - inversion H2; subst; simpl in *.
    edestruct H0; eauto.
    exists (x, nil); simpl; intuition.
  - inversion H2; subst; simpl in *.
    edestruct H0; try apply H4.
    edestruct IHl; eauto.
    exists (fst x0, x :: snd x0); simpl.
    intuition.
Qed.
Theorem NEforall2_d_map : forall T1 T2 A B (p : T1 -> T2 -> Prop) ( q : A -> B -> Prop) l1 (f1 : A -> T1) l2 (f2 : B -> T2),
  (forall a b n, a = nthd n l1 -> b = nthd n l2 -> q a b -> p (f1 a) (f2 b)) ->
  NEforall2 q l1 l2 ->
  NEforall2 p (d_map f1 l1) (d_map f2 l2).
(* hint proof tokens: 253 *)
Proof.
  intros.
  unfold NEforall2, d_map in *.
  simpl; split.
  specialize (H (fst l1) (fst l2) 0).
  apply H.
  rewrite nthd_0; eauto.
  rewrite nthd_0; eauto.
  intuition.
  intuition.
  assert (length (snd l1) = length (snd l2)).
  eapply forall2_length; eauto.
  eapply forall2_map2_selN with (q := q); auto; intros.
  destruct (lt_dec n (length (snd l1))).
  - eapply H with (n := (length (snd l1) - n)); unfold nthd; subst; eauto.
    replace (length (snd l1) - (length (snd l1) - n)) with n by lia; eauto.
    replace (length (snd l2) - (length (snd l1) - n)) with n by lia; eauto.
  - rewrite selN_oob in * by lia; subst.
    eapply H; auto.
    rewrite nthd_0; auto.
    rewrite nthd_0; auto.
Qed.
Lemma NEforall_d_in : forall T (p : T -> Prop) l x,
  NEforall p l ->
  d_in x l ->
  p x.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma NEforall_d_in':
  forall T (p : T -> Prop) l, (forall x, d_in x l -> p x) -> NEforall p l.
Proof.
(* original proof tokens: 68 *)
(* generated proof tokens: 50 *)

unfold NEforall. 
intros.
destruct l as [h t].
split; [ apply H; left; reflexivity | apply Forall_forall; intros; apply H; right; auto ].
Qed.

Lemma NEforall2_length : forall T1 T2 (p : T1 -> T2 -> Prop) l1 l2,
  NEforall2 p l1 l2 ->
  Datatypes.length (snd l1) = Datatypes.length (snd l2).
(* hint proof tokens: 24 *)
Proof.
  unfold NEforall2; intuition.
  apply forall2_length in H1; auto.
Qed.
Lemma NEforall2_d_in : forall T1 T2 (p : T1 -> T2 -> Prop) l1 l2 x y n,
  NEforall2 p l1 l2 ->
  x = nthd n l1 ->
  y = nthd n l2 ->
  p x y.
(* hint proof tokens: 104 *)
Proof.
  intros.
  rewrite H0.
  rewrite H1.
  unfold nthd.
  apply NEforall2_length in H as H'.
  destruct n.

  repeat rewrite selN_oob by lia.
  firstorder.

  case_eq (Datatypes.length (snd l1)); intros.
  repeat rewrite selN_oob by lia.
  firstorder.

  rewrite <- H'. rewrite H2.
  eapply forall2_selN.
  firstorder.
  lia.
Qed.
Lemma NEforall2_latest: forall (T1 T2 : Type) (p : T1 -> T2 -> Prop) (l1 : nelist T1)
    (l2 : nelist T2),
  NEforall2 p l1 l2 -> p (l1 !!) (l2 !!).
Proof.
(* original proof tokens: 43 *)
unfold NEforall2. intros. destruct l1, l2. simpl in H. 
destruct H as [H1 H2]. simpl in *. 
auto.
(* No more tactics to try *)
Admitted.

Definition list2nelist A def (l: list A) : nelist A :=
  match l with
  | nil => def
  | h::t => pushdlist (rev t) (singular h)
  end.
Definition nelist2list A (nel: nelist A) : list A := (fst nel)::(snd nel).
Lemma nelist2list2nelist: forall A (l: nelist A) def, 
  list2nelist def (nelist2list l) = l.
(* hint proof tokens: 53 *)
Proof.
  intros.
  unfold list2nelist, nelist2list.
  unfold singular.
  rewrite pushdlist_app.
  rewrite rev_involutive.
  rewrite app_nil_r.
  symmetry; apply surjective_pairing.
Qed.
Lemma list2nelist2list: forall A (l: list A) def, 
  l<>nil -> nelist2list (list2nelist def l) = l.
(* hint proof tokens: 60 *)
Proof.
  intros.
  destruct l.
  destruct H; reflexivity.
  unfold list2nelist.
  unfold singular.
  rewrite pushdlist_app.
  rewrite rev_involutive.
  rewrite app_nil_r.
  unfold nelist2list; reflexivity.
Qed.
