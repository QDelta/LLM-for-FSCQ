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
(* skipped proof tokens: 30 *)
Admitted.
End ListRevSel.
Section NonEmptyList.
Variable T : Type.
Definition nelist  := (T * list T)%type.
Definition singular x : nelist := (x, nil).
Definition latest (ds : nelist) := hd (fst ds) (snd ds).
Definition latest_cons : forall d0 d ds, latest (d0, d :: ds) = d.
(* hint proof tokens: 11 *)
Proof.
    firstorder.
  Qed.
Definition nthd n (ds : nelist) := selN (snd ds) (length (snd ds) - n) (fst ds).
Lemma nthd_0 : forall ds, nthd 0 ds = fst ds.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma nthd_oob : forall ds n, n >= length (snd ds) -> nthd n ds = latest ds.
Proof.
(* skipped proof tokens: 44 *)
Admitted.
Definition pushd (d : T) (ds : nelist) : nelist :=
      (fst ds, d :: snd ds).
Theorem latest_pushd : forall d ds,
    latest (pushd d ds) = d.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Fixpoint pushdlist (dlist : list T) (ds : nelist) : nelist :=
      match dlist with
      | nil => ds
      | d :: dlist' => pushdlist dlist' (pushd d ds)
      end.
Definition popn (n : nat) (ds : nelist) : nelist :=
      (nthd n ds, cuttail n (snd ds)).
Lemma popn_0 : forall ds,
    popn 0 ds = ds.
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Lemma popn_oob : forall ds n,
    n >= length (snd ds) -> popn n ds = (latest ds, nil).
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma singular_latest : forall ds, snd ds = nil -> latest ds = fst ds.
Proof.
(* original proof tokens: 23 *)
(* generated proof tokens: 38 *)

Proof.
  intros ds H.
  unfold latest.
  destruct ds as [x xs].
  simpl in *.
  rewrite H.
  reflexivity.
Qed.

Lemma singular_nthd : forall ds n, snd ds = nil -> nthd n ds = fst ds.
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Lemma popn_oob_singular' : forall ds n,
    n >= length (snd ds) -> snd (popn n ds) = nil.
(* hint proof tokens: 25 *)
Proof.
    unfold popn; intros.
    rewrite cuttail_oob by lia; auto.
  Qed.
Lemma popn_oob_singular : forall ds n,
    n >= length (snd ds) -> popn n ds = singular (latest ds).
Proof.
(* skipped proof tokens: 34 *)
Admitted.
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
(* hint proof tokens: 102 *)
Proof.
    intros.
    replace (S n) with (1 + n) by lia.
    rewrite <- popn_popn.
    unfold popn at 2; simpl.
    rewrite cuttail_tail, cuttail_0.
    unfold nthd; simpl.
    rewrite app_length; simpl.
    rewrite selN_app2 by lia.
    replace (length ds + 1 - 1 - length ds) with 0 by lia; simpl; auto.
  Qed.
Lemma pushdlist_app : forall d l' l,
    pushdlist l' (d, l) = (d, (rev l') ++ l)%list.
Proof.
(* skipped proof tokens: 38 *)
Admitted.
Lemma nthd_popn : forall m n ds,
    nthd n (popn m ds) = nthd (m + n) ds.
(* hint proof tokens: 152 *)
Proof.
    unfold popn, nthd; simpl; intros.
    rewrite cuttail_length, Nat.sub_add_distr.
    destruct (lt_dec m (length (snd ds))).
    destruct n.
    rewrite Nat.sub_0_r.
    rewrite selN_oob; auto.
    rewrite cuttail_length; auto.
    rewrite selN_cuttail; auto.
    erewrite selN_inb by lia; eauto.
    rewrite cuttail_length; lia.
    replace (length (snd ds) - m - n) with 0 by lia.
    rewrite cuttail_oob by lia; simpl.
    replace (length (snd ds) - m) with 0 by lia; auto.
 Qed.
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
(* hint proof tokens: 67 *)
Proof.
    intros.
    assert (In d (rev l1) \/ d_in d (a, l2)).
    apply d_in_pushdlist.
    rewrite pushdlist_app. rewrite rev_involutive. eauto.
    intuition.
    left. apply in_rev. eauto.
  Qed.
Theorem nthd_in_ds : forall ds n,
    d_in (nthd n ds) ds.
(* hint proof tokens: 64 *)
Proof.
    unfold nthd, d_in.
    destruct ds.
    destruct n.
    - left.
      apply selN_oob. lia.
    - destruct l; simpl snd.
      + eauto.
      + right.
        apply in_selN.
        simpl; lia.
  Qed.
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
(* hint proof tokens: 16 *)
Proof.
    unfold d_in; simpl; intuition.
  Qed.
Lemma d_in_pushd : forall ds d d',
    d_in d (pushd d' ds) ->
    d = d' \/ d_in d ds.
Proof.
(* skipped proof tokens: 19 *)
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
(* skipped proof tokens: 75 *)
Admitted.
Lemma pushd_latest: forall l d,
    latest (pushd d l)  = d.
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Lemma length_popn : forall n ds,
    length (snd (popn n ds)) = length (snd ds) - n.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma latest_popn : forall n ds,
    latest (popn n ds) = latest ds.
(* hint proof tokens: 69 *)
Proof.
    intros.
    do 2 rewrite latest_nthd.
    rewrite length_popn.
    rewrite nthd_popn.
    destruct (le_dec n (length (snd ds))).
    f_equal; lia.
    rewrite nthd_oob, latest_nthd; auto.
    lia.
  Qed.
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
(* hint proof tokens: 14 *)
Proof.
    induction l; eauto.
  Qed.
Lemma nelist_list_subset : forall ds ds',
    NEListSubset ds ds' <-> ListSubset (snd ds ++ [fst ds]) (snd ds' ++ [fst ds']).
Proof.
(* skipped proof tokens: 473 *)
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
Proof.
(* skipped proof tokens: 43 *)
Admitted.
Lemma nelist_subset_latest : forall ds,
    NEListSubset ds (latest ds, nil).
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

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
(* skipped proof tokens: 23 *)
Admitted.
Lemma nelist_subset_popn1 : forall ds ds',
    NEListSubset (popn 1 ds) ds' ->
    NEListSubset ds ds'.
(* hint proof tokens: 386 *)
Proof.
    unfold popn, nthd; intros.
    destruct ds, ds'; simpl in *.
    generalize dependent l0.
    induction l.
    - unfold cuttail in *; simpl in *; eauto.
    - intros.
      destruct l.
      + unfold cuttail in *; simpl in *.
        inversion H; subst.
        replace (t, [t0]) with (pushd t0 (t, nil)) by reflexivity.
        eapply NESubsetHead.
      + replace (selN (a :: t1 :: l) (length (a :: t1 :: l) - 1) t) with (selN (t1 :: l) (length (t1 :: l) - 1) t) in H.
        2: simpl; rewrite <- minus_n_O; eauto.
        rewrite cuttail_cons in H by ( simpl; lia ).
        inversion H; subst.
        * replace (t, t0 :: t1 :: l) with (pushd t0 (t, t1 :: l)) by reflexivity.
          eapply NESubsetHead.
        * replace (t, a :: t1 :: l) with (pushd a (t, t1 :: l)) by reflexivity.
          replace (fst ds', a :: snd ds') with (pushd a (fst ds', snd ds')) by reflexivity.
          eapply NESubsetIn.
          eapply IHl.
          destruct ds, ds'; simpl in *; subst; eauto.
        * replace (t, a :: t1 :: l) with (pushd a (t, t1 :: l)) by reflexivity.
          eapply NESubsetNotIn.
          eapply IHl.
          destruct ds; simpl in *; subst; eauto.
  Qed.
Lemma nelist_subset_popn : forall n ds ds',
    NEListSubset (popn n ds) ds' ->
    NEListSubset ds ds'.
Proof.
(* skipped proof tokens: 73 *)
Admitted.
Lemma nelist_subset_nthd_latest : forall n ds,
    n < length (snd ds) ->
    NEListSubset ds (nthd n ds, latest ds :: nil).
Proof.
(* skipped proof tokens: 89 *)
Admitted.
Lemma nelist_subset_popn1' : forall ds ds',
    NEListSubset ds ds' ->
    NEListSubset ds (popn 1 ds').
Proof.
(* skipped proof tokens: 326 *)
Admitted.
Lemma nelist_subset_popn' : forall n ds ds',
    NEListSubset ds ds' ->
    NEListSubset ds (popn n ds').
Proof.
(* skipped proof tokens: 65 *)
Admitted.
Lemma pushd_length : forall ds d,
    length (snd (pushd d ds)) = S (length (snd ds)).
(* hint proof tokens: 18 *)
Proof.
    intros; unfold pushd; simpl; auto.
  Qed.
Lemma pushdlist_length: forall dlist ds,
    length (snd (pushdlist dlist ds)) =
    length dlist + length (snd ds).
(* hint proof tokens: 37 *)
Proof.
    induction dlist.
    reflexivity.
    simpl.
    intros.
    rewrite IHdlist.
    rewrite pushd_length.
    lia.
  Qed.
Lemma nthd_pushd : forall l t n d,
    n <= length l
    -> nthd n (pushd d (t, l)) = nthd n (t, l).
Proof.
(* skipped proof tokens: 81 *)
Admitted.
Lemma nthd_pushd' : forall ds n d,
    n <= length (snd ds)
    -> nthd n (pushd d ds) = nthd n ds.
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Lemma nthd_pushd_latest : forall l t d n,
    n = S (length l)
    -> nthd n (pushd d (t, l)) = d.
(* hint proof tokens: 29 *)
Proof.
    unfold nthd, pushd; intros.
    simpl; subst.
    rewrite minus_diag; auto.
  Qed.
Lemma nthd_pushd_latest' : forall ds d n,
    n = S (length (snd ds))
    -> nthd n (pushd d ds) = d.
Proof.
(* skipped proof tokens: 24 *)
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
(* skipped proof tokens: 24 *)
Admitted.
Lemma d_map_fst : forall A B (f : A -> B) ds,
  fst (d_map f ds) = f (fst ds).
(* hint proof tokens: 14 *)
Proof.
  unfold d_map; intros; auto.
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
(* hint proof tokens: 80 *)
Proof.
  intros.
  apply d_in_In in H.
  replace (f (fst ds) :: map f (snd ds)) with (map f ((fst ds) :: (snd ds))) in H by reflexivity.
  apply in_map_iff in H.
  destruct H.
  eexists; intuition eauto.
  apply d_in_In'; eauto.
Qed.
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
(* hint proof tokens: 15 *)
Proof.
  firstorder; simpl.
  firstorder.
Qed.
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
(* hint proof tokens: 33 *)
Proof.
  unfold NEforall, d_in.
  intuition.
  subst; eauto.
  eapply Forall_forall; eauto.
Qed.
Lemma NEforall_d_in':
  forall T (p : T -> Prop) l, (forall x, d_in x l -> p x) -> NEforall p l.
Proof.
(* skipped proof tokens: 68 *)
Admitted.
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
Proof.
(* skipped proof tokens: 104 *)
Admitted.
Lemma NEforall2_latest: forall (T1 T2 : Type) (p : T1 -> T2 -> Prop) (l1 : nelist T1)
    (l2 : nelist T2),
  NEforall2 p l1 l2 -> p (l1 !!) (l2 !!).
Proof.
(* skipped proof tokens: 43 *)
Admitted.
Definition list2nelist A def (l: list A) : nelist A :=
  match l with
  | nil => def
  | h::t => pushdlist (rev t) (singular h)
  end.
Definition nelist2list A (nel: nelist A) : list A := (fst nel)::(snd nel).
Lemma nelist2list2nelist: forall A (l: nelist A) def, 
  list2nelist def (nelist2list l) = l.
Proof.
(* skipped proof tokens: 53 *)
Admitted.
Lemma list2nelist2list: forall A (l: list A) def, 
  l<>nil -> nelist2list (list2nelist def l) = l.
Proof.
(* skipped proof tokens: 60 *)
Admitted.
