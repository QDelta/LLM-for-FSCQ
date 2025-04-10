Require Import Mem.
Require Import List Lia Ring Word Pred PredCrash Prog Hoare SepAuto BasicProg Array ListUtils.
Require Import FunctionalExtensionality.
Require Import Permutation.
Import PeanoNat.
Set Implicit Arguments.
Section LISTPRED.
Set Default Proof Using "Type".
Variable T : Type.
Variable AT : Type.
Variable AEQ : EqDec AT.
Variable V : Type.
Variable prd : T -> @pred AT AEQ V.
Fixpoint listpred (ts : list T) :=
    match ts with
    | nil => emp
    | t :: ts' => (prd t) * listpred ts'
    end%pred.
Lemma listpred_nil:
    listpred nil = emp.
(* hint proof tokens: 16 *)
Proof.
    unfold listpred; intros; auto.
  Qed.
Theorem listpred_fwd : forall l i def, 
    i < length l ->
      listpred l =p=> listpred (firstn i l) * (prd (selN l i def)) * listpred (skipn (S i) l).
(* hint proof tokens: 34 *)
Proof.
    induction l; simpl; intros; [lia |].
    destruct i; simpl; cancel.
    apply IHl; lia.
  Qed.
Theorem listpred_bwd : forall l i def, 
    i < length l ->
      listpred (firstn i l) * (prd (selN l i def)) * listpred (skipn (S i) l) =p=> listpred l.
(* hint proof tokens: 70 *)
Proof.
    induction l; simpl; intros; [lia |].
    destruct i; [cancel | simpl].
    destruct l; simpl in H; [lia |].
    cancel.
    eapply pimpl_trans; [| apply IHl ].
    cancel.
    apply pimpl_refl.
    lia.
  Qed.
Theorem listpred_extract : forall l i def,
    i < length l ->
    listpred l =p=> exists F, F * prd (selN l i def).
(* hint proof tokens: 27 *)
Proof.
    intros; rewrite listpred_fwd with (def:=def) by eauto; cancel.
  Qed.
Theorem listpred_pick : forall x l, 
    In x l -> listpred l =p=> exists F, prd x * F.
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_inj: forall l1 l2,
     l1 = l2 -> listpred l1 <=p=> listpred l2.
Proof.
(* original proof tokens: 14 *)

(* No more tactics to try *)
Admitted.

Definition sep_star_fold : (T -> @pred AT AEQ V -> @pred AT AEQ V) := fun x => sep_star (prd x).
Definition listpred' := fold_right sep_star_fold emp.
Theorem listpred_listpred': forall l,
    listpred l = listpred' l.
(* hint proof tokens: 27 *)
Proof.
    induction l; unfold listpred, listpred', sep_star_fold, fold_right; auto.
  Qed.
Theorem listpred'_app_fwd: forall l1 l2,
    listpred' (l1 ++ l2) =p=> listpred' l1 * listpred' l2.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Theorem listpred'_app_bwd: forall l1 l2,
    listpred' l1 * listpred' l2 =p=> listpred' (l1 ++ l2).
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_app: forall l1 l2,
    listpred (l1 ++ l2) <=p=> listpred l1 * listpred l2.
(* hint proof tokens: 55 *)
Proof.
    intros; replace listpred with listpred'.
    unfold piff; split.
    apply listpred'_app_fwd.
    apply listpred'_app_bwd.
    apply functional_extensionality.
    apply listpred_listpred'.
  Qed.
Theorem listpred_isolate : forall l i def,
    i < length l ->
    listpred l <=p=> listpred (removeN l i) * prd (selN l i def).
(* hint proof tokens: 60 *)
Proof.
    intros.
    unfold removeN.
    rewrite listpred_app.
    unfold piff; split.
    rewrite listpred_fwd by eauto; cancel.
    eapply pimpl_trans2.
    apply listpred_bwd; eauto.
    cancel.
  Qed.
Theorem listpred_split : forall l n,
    listpred l <=p=> listpred (firstn n l) * listpred (skipn n l).
(* hint proof tokens: 41 *)
Proof.
    intros.
    setoid_rewrite <- firstn_skipn with (n := n) at 1.
    rewrite listpred_app.
    split; cancel.
  Qed.
Theorem listpred_isolate_fwd : forall l i def,
    i < length l ->
    listpred l =p=> listpred (removeN l i) * prd (selN l i def).
(* hint proof tokens: 19 *)
Proof.
    intros.
    apply listpred_isolate; auto.
  Qed.
Theorem listpred_updN : forall l i v,
    i < length l ->
    listpred (updN l i v) <=p=> listpred (removeN l i) * prd v.
(* hint proof tokens: 52 *)
Proof.
    intros; rewrite listpred_isolate with (def:=v);
       [ | rewrite length_updN; eauto].
    rewrite removeN_updN.
    rewrite selN_updN_eq; auto.
  Qed.
Theorem listpred_updN_selN: forall l i v def,
    i < length l ->
    prd (selN l i def) =p=> prd v ->
    listpred l =p=> listpred (updN l i v).
(* hint proof tokens: 44 *)
Proof.
    intros.
    rewrite listpred_updN by auto.
    rewrite listpred_isolate with (def:=def) at 1 by eauto.
    cancel; auto.
  Qed.
Theorem listpred_nodup : forall l m,
    (forall x y : T, {x = y} + {x <> y}) ->
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    listpred l m -> NoDup l.
Proof.
(* original proof tokens: 169 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_nodup_piff : forall l,
    (forall x y : T, {x = y} + {x <> y}) ->
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    listpred l <=p=> [[ NoDup l ]] * listpred l.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_nodup_F : forall l m,
    (forall x y : T, {x = y} + {x <> y}) ->
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    (exists F, F * listpred l)%pred m -> NoDup l.
(* hint proof tokens: 44 *)
Proof.
    intros.
    destruct_lift H0.
    rewrite listpred_nodup_piff in H0 by eauto.
    destruct_lift H0.
    eauto.
  Qed.
Lemma listpred_permutation: forall a b,
    Permutation a b ->
    listpred a <=p=> listpred b.
(* hint proof tokens: 52 *)
Proof.
    intros.
    induction H; cbn; auto.
    rewrite IHPermutation. auto.
    split; cancel.
    rewrite IHPermutation1.
    rewrite IHPermutation2.
    auto.
  Qed.
Theorem listpred_remove :
    forall (dec : forall x y : T, {x = y} + {x <> y}) x l,
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    In x l ->
    listpred l =p=> prd x * listpred (remove dec x l).
Proof.
(* original proof tokens: 72 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_remove' :
    forall (dec : forall x y : T, {x = y} + {x <> y}) x l,
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    NoDup l ->
    In x l ->
    prd x * listpred (remove dec x l) =p=> listpred l.
(* hint proof tokens: 66 *)
Proof.
    intros.
    induction l.
    cancel.
    simpl; destruct (dec x a); subst.
    - inversion H0. rewrite remove_not_In; eauto.
    - simpl; cancel.
      rewrite <- IHl. cancel. inversion H0. eauto. eauto.
  Qed.
Theorem listpred_remove_piff :
    forall (dec : forall x y : T, {x = y} + {x <> y}) x l,
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    NoDup l ->
    In x l ->
    listpred l <=p=> prd x * listpred (remove dec x l).
(* hint proof tokens: 30 *)
Proof.
    split.
    eapply listpred_remove; eauto.
    eapply listpred_remove'; eauto.
  Qed.
Theorem listpred_eq : forall l m1 m2,
    (forall x ma mb, prd x ma -> prd x mb -> ma = mb) ->
    listpred l m1 -> listpred l m2 -> m1 = m2.
(* hint proof tokens: 85 *)
Proof.
    induction l; simpl; intros.
    - apply emp_complete; eauto.
    - unfold sep_star in *; rewrite sep_star_is in *; unfold sep_star_impl in *.
      repeat deex.
      assert (m2 = m0) by eauto; subst.
      assert (m4 = m3) by eauto; subst.
      reflexivity.
  Qed.
Theorem listpred_emp : forall l,
    (forall x, In x l -> prd x =p=> emp) ->
    listpred l =p=> emp.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_emp_piff : forall l,
    (forall x, In x l -> prd x <=p=> emp) ->
    listpred l <=p=> emp.
(* hint proof tokens: 49 *)
Proof.
    induction l; intros.
    rewrite listpred_nil; auto.
    simpl.
    rewrite H; intuition.
    rewrite IHl.
    split; cancel.
    intros.
    rewrite H; intuition.
  Qed.
Lemma listpred_partition: forall f (l : list T),
    let p := partition f l in
    listpred l <=p=> listpred (fst p) * listpred (snd p).
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Lemma listpred_rev: forall l,
    listpred l <=p=> listpred (rev l).
(* hint proof tokens: 37 *)
Proof.
    induction l; cbn; intros.
    split; cancel.
    rewrite listpred_app.
    rewrite IHl.
    split; cancel.
  Qed.
End LISTPRED.
Theorem listpred_lift : forall T l AT AEQ V prd F G,
  (forall x, In x l -> prd x <=p=> [[ F x ]] * G x) ->
  @listpred T AT AEQ V prd l <=p=> [[ Forall F l ]] * listpred G l.
(* hint proof tokens: 49 *)
Proof.
  intros; induction l.
  split; cancel.
  simpl; rewrite H; intuition.
  rewrite IHl.
  split; cancel; inversion H1; auto.
  intros.
  apply H; intuition.
Qed.
Theorem listpred_unify : forall T l1 l2 AT AEQ V f F1 F2 m,
    (forall Fa Fb a b, In a l1 -> In b l2 -> (Fa * f a)%pred m -> (Fb * f b)%pred m -> a = b) ->
    (F1 * @listpred T AT AEQ V f l1)%pred m -> (F2 * listpred f l2)%pred m ->
    length l1 = length l2 ->
    l1 = l2.
Proof.
(* original proof tokens: 138 *)

(* No more tactics to try *)
Admitted.

Lemma listpred_pimpl_replace: forall T AT V M (l : list T) (F G : T -> @pred AT M V),
       (forall x, In x l -> F x =p=> G x) ->
       listpred F l =p=> listpred G l.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma listpred_piff_replace : forall A B AT M l F G,
  (forall x, In x l -> F x <=p=> G x) -> @listpred A B AT M F l <=p=> listpred G l.
(* hint proof tokens: 43 *)
Proof.
  induction l; intros; split; cancel.
  rewrite IHl, H by auto; cancel.
  rewrite IHl, H by (intuition; symmetry; auto); cancel.
Qed.
Lemma listpred_ptsto_notindomain : forall AT AEQ V (t : list AT) x (m : @Mem.mem _ AEQ V),
  listpred (fun a => (a |->?)%pred) t m ->
  ~In x t ->
  notindomain x m.
(* hint proof tokens: 84 *)
Proof.
  induction t; cbn; intros; unfold notindomain.
  cbv [emp] in *; auto.
  intuition.
  revert H.
  unfold_sep_star.
  intuition repeat deex.
  eapply mem_union_sel_none.
  unfold exis in *. deex.
  eapply ptsto_ne; eauto.
  eapply IHt; eauto.
Qed.
Section LISTMATCH.
Set Default Proof Using "Type".
Variable A : Type.
Variable B : Type.
Variable AT : Type.
Variable AEQ : EqDec AT.
Variable V : Type.
Variable prd : A -> B -> @pred AT AEQ V.
Definition pprd := prod_curry prd.
Definition listmatch (a : list A) (b : list B) :=
    ([[ length a = length b ]] *
     listpred pprd (List.combine a b))%pred.
Lemma listmatch_length : forall a b m,
    (listmatch a b)%pred m -> length a = length b.
(* hint proof tokens: 22 *)
Proof.
    unfold listmatch; intros.
    destruct_lift H; auto.
  Qed.
Lemma listmatch_length_r : forall F a b m,
    (F * listmatch a b)%pred m -> length a = length b.
(* hint proof tokens: 22 *)
Proof.
    unfold listmatch; intros.
    destruct_lift H; auto.
  Qed.
Lemma listmatch_length_l : forall F a b m,
    (listmatch a b * F)%pred m -> length a = length b.
(* hint proof tokens: 22 *)
Proof.
    unfold listmatch; intros.
    destruct_lift H; auto.
  Qed.
Lemma listmatch_length_pimpl : forall a b,
    listmatch a b =p=> (listmatch a b) * [[ length a = length b ]].
Proof.
(* original proof tokens: 14 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_cons: forall (a : list A) (b : list B) x y,
    listmatch (x :: a) (y :: b) <=p=> prd x y * listmatch a b.
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_isolate : forall a b i ad bd,
    i < length a -> i < length b ->
    listmatch a b <=p=>
    listmatch (removeN a i) (removeN b i) * prd (selN a i ad) (selN b i bd).
Proof.
(* original proof tokens: 225 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_extract : forall a b i ad bd,
    i < length a ->
    listmatch a b =p=>
    [[ length a = length b ]] * 
    listmatch (removeN a i) (removeN b i) * prd (selN a i ad) (selN b i bd).
Proof.
(* original proof tokens: 86 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_updN_removeN : forall a b i av bv,
    i < length a -> i < length b ->
    listmatch (updN a i av) (updN b i bv) <=p=>
    listmatch (removeN a i) (removeN b i) * (prd av bv).
Proof.
(* original proof tokens: 141 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_updN_selN: forall a b i av bv ad bd,
    i < length a -> i < length b ->
    prd (selN a i ad) (selN b i bd) =p=> prd av bv ->
    listmatch a b =p=> listmatch (updN a i av) (updN b i bv).
(* hint proof tokens: 48 *)
Proof.
    intros.
    rewrite listmatch_updN_removeN by auto.
    rewrite listmatch_isolate with (ad := ad) (bd := bd) by eauto.
    cancel; auto.
  Qed.
Theorem listmatch_updN_selN_r: forall F a b i av bv ad bd,
    i < length a -> i < length b ->
    (prd (selN a i ad) (selN b i bd)) * F =p=> prd av bv ->
    (listmatch a b) * F =p=> listmatch (updN a i av) (updN b i bv).
Proof.
(* original proof tokens: 53 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_app_tail: forall F a b av bv,
    length a = length b ->
    F =p=> prd av bv ->
    (listmatch a b) * F =p=> listmatch (a ++ av :: nil) (b ++ bv :: nil).
Proof.
(* original proof tokens: 89 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_app : forall a1 b1 a2 b2,
    listmatch a1 b1 * listmatch a2 b2 =p=> listmatch (a1 ++ a2) (b1 ++ b2).
(* hint proof tokens: 40 *)
Proof.
    unfold listmatch; intros; cancel.
    repeat rewrite combine_app by auto.
    rewrite listpred_app; cancel.
    repeat rewrite app_length; lia.
  Qed.
Theorem listmatch_app_rev : forall a1 b1 a2 b2,
    length a1 = length b1 \/ length a2 = length b2 ->
    listmatch (a1 ++ a2) (b1 ++ b2) =p=> listmatch a1 b1 * listmatch a2 b2.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_split : forall a b n,
    listmatch a b <=p=> listmatch (firstn n a) (firstn n b) * listmatch (skipn n a) (skipn n b).
Proof.
(* original proof tokens: 103 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_emp : forall l1 l2,
    (forall x y, In x l1 -> In y l2 -> prd x y =p=> emp) ->
    listmatch l1 l2 =p=> emp.
(* hint proof tokens: 58 *)
Proof.
    intros.
    unfold listmatch.
    rewrite listpred_emp.
    cancel.
    intros; destruct x; simpl.
    apply H; solve [eapply in_combine_l; eauto |eapply in_combine_r; eauto].
  Qed.
Theorem listmatch_emp_piff : forall l1 l2,
    (forall x y, In x l1 -> In y l2 -> prd x y <=p=> emp) ->
    listmatch l1 l2 <=p=> [[ length l1 = length l2 ]].
(* hint proof tokens: 83 *)
Proof.
    split.
    rewrite listmatch_length_pimpl; cancel.
    apply listmatch_emp; intuition.
    rewrite H; auto.
    unfold listmatch; rewrite listpred_emp_piff.
    cancel.
    intros; destruct x; simpl.
    apply H; solve [eapply in_combine_l; eauto |eapply in_combine_r; eauto].
  Qed.
Theorem listmatch_repeat_l : forall v n l2,
    listmatch (repeat v n) l2 <=p=> [[ n = length l2 ]] * listpred (prd v) l2.
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_repeat_r : forall v n l1,
    listmatch l1 (repeat v n) <=p=> [[ length l1 = n]] * listpred (fun x => prd x v) l1.
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Lemma listpred_exis_listmatch: forall (a : list A),
    listpred (fun a => exists b, prd a b) a =p=> exists b, listmatch a b.
(* hint proof tokens: 53 *)
Proof.
    induction a; cbn; intros.
    exists nil.
    unfold listmatch. pred_apply; cancel.
    rewrite IHa.
    cancel.
    rewrite listmatch_cons with (b := b0).
    cancel.
  Qed.
Lemma listmatch_rev: forall a b,
    listmatch a b <=p=> listmatch (rev a) (rev b).
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

End LISTMATCH.
Theorem listmatch_lift : forall A B AT AEQ V prd (l1 : list A) (l2 : list B) F P,
  (forall x y, In x l1 -> In y l2 -> prd x y ⇦⇨ ⟦⟦ P x y ⟧⟧ ✶ F x y) ->
  @listmatch A B AT AEQ V prd l1 l2 <=p=> [[ Forall2 P l1 l2]] * listmatch F l1 l2.
Proof.
(* original proof tokens: 84 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_lift_l : forall A B AT AEQ V prd (l1 : list A) (l2 : list B) F P,
  (forall x y, In x l1 -> In y l2 -> prd x y ⇦⇨ ⟦⟦ P x ⟧⟧ ✶ F x y) ->
  @listmatch A B AT AEQ V prd l1 l2 <=p=> [[ Forall P l1 ]] * listmatch F l1 l2.
Proof.
(* original proof tokens: 123 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_pimpl_replace: forall A B AT T M la lb (F G : A -> B -> @pred AT M T),
       (forall x y, In x la -> In y lb -> F x y =p=> G x y) ->
       listmatch F la lb =p=> listmatch G la lb.
(* hint proof tokens: 37 *)
Proof.
  unfold listmatch.
  intros.
  rewrite listpred_pimpl_replace; cancel.
  eauto using in_combine_l, in_combine_r.
Qed.
Lemma listmatch_piff_replace : forall A B AT T M l1 l2 F G,
  (forall x y, In x l1 -> In y l2 -> F x y <=p=> G x y) -> @listmatch A B AT M T F l1 l2 <=p=> listmatch G l1 l2.
Proof.
(* original proof tokens: 65 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_nodup: forall AT AEQ V (a : list AT) (b : list V) (F : @pred AT AEQ V) m,
  (F * listmatch (fun x y => x |-> y) a b)%pred m -> NoDup a.
Proof.
(* original proof tokens: 210 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_listpred_seq : forall V l st n,
  length l = n ->
  arrayN (@ptsto _ _ V) st l =p=> listpred (fun a => a |->?) (seq st n).
(* hint proof tokens: 32 *)
Proof.
  induction l; destruct n; simpl; intros; try lia; auto.
  rewrite IHl.
  cancel.
  lia.
Qed.
Lemma arrayN_listpred_seq_fp : forall V FP l st n,
  length l = n ->
  Forall FP l ->
  arrayN (@ptsto _ _ V) st l =p=> listpred (fun a => exists v, a |-> v * [[ FP v ]]) (seq st n).
(* hint proof tokens: 52 *)
Proof.
  induction l; destruct n; simpl; intros; try lia; auto.
  inversion H0; subst.
  rewrite IHl; auto.
  cancel.
  replace (length l) with n by lia.
  cancel.
Qed.
Lemma listmatch_sym : forall AT AEQ V A B (al : list A) (bl : list B) f,
  (@listmatch _ _ AT AEQ V) f al bl <=p=>
  listmatch (fun b a => f a b) bl al.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_map_l : forall AT AEQ V A B C al bl f (g : A -> C),
  (@listmatch C B AT AEQ V) f (map g al) bl <=p=>
  (@listmatch A B _ _ _) (fun a b => f (g a) b) al bl.
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_map_r : forall AT AEQ V A B C al bl f (g : B -> C),
  (@listmatch A C AT AEQ V) f al (map g bl) <=p=>
  (@listmatch A B _ _ _) (fun a b => f a (g b)) al bl.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_map : forall AT AEQ V A B A' B' al bl f (fa : A -> A') (fb : B -> B'),
  (@listmatch A B AT AEQ V) (fun a b => f (fa a) (fb b)) al bl <=p=>
  (@listmatch A' B' _ _ _) f (map fa al) (map fb bl).
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma listpred_map : forall AT AEQ V A B l f (g : A -> B),
  @listpred B AT AEQ V f (map g l) <=p=>
  @listpred A AT AEQ V (fun a => f (g a)) l.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_ptsto_listpred : forall AT AEQ V (al : list AT) (vl : list V),
  listmatch (fun v a => a |-> v) vl al =p=>
  (@listpred _ _ AEQ _) (fun a => a |->?) al.
Proof.
(* original proof tokens: 60 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_lift_r : forall AT AEQ V A C l1 l2 f F P,
  (forall x y, In x l1 -> In y l2 -> f x y <=p=> ([[ P y ]] * F x y)%pred) ->
  @listmatch A C AT AEQ V f l1 l2 <=p=> [[ Forall P l2 ]] * listmatch F l1 l2.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_unify : forall A B la lb l1 l2 AT AEQ V F1 F2 (f : A -> B -> @pred AT AEQ V) m,
  (forall Fa Fb xa xb ya yb, In xa la -> In xb lb -> In ya l1 -> In yb l2 ->
  (Fa * f xa ya)%pred m -> (Fb * f xb yb)%pred m -> (xa = xb /\ ya = yb)) ->
  (F1 * listmatch f la l1)%pred m -> (F2 * listmatch f lb l2)%pred m ->
  length la = length lb ->
  la = lb /\ l1 = l2.
Proof.
(* original proof tokens: 225 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_unify_r : forall A B l l1 l2 AT AEQ V F1 F2 (f : A -> B -> @pred AT AEQ V) m,
  (forall Fa Fb x ya yb, In x l -> In ya l1 -> In yb l2 ->
  (Fa * f x ya)%pred m -> (Fb * f x yb)%pred m -> (ya = yb)) ->
  (F1 * listmatch f l l1)%pred m -> (F2 * listmatch f l l2)%pred m ->
  l1 = l2.
(* hint proof tokens: 187 *)
Proof.
  induction l; intros; destruct l1, l2; auto.
  all : unfold listmatch in *;
        destruct_lift H0; destruct_lift H1;
        match goal with
        | [ H : 0 = S _ |- _] => inversion H
        | [ H : S _ = 0 |- _] => inversion H
        | [ |- _] => idtac
        end.
  f_equal; [> eapply H | eapply IHl]; intros;
    try match goal with
    | [ |- _ \/ _] => left; eauto
    | [ |- _ = _ ] => eapply H
    end; eauto.
  all : match goal with
  | [H : _ |- _] => solve [eapply pimpl_apply; [> | exact H]; cancel]
  end.
Qed.
Lemma listmatch_unify_l : forall A B l la lb AT AEQ V F1 F2 (f : A -> B -> @pred AT AEQ V) m,
  (forall Fa Fb xa xb y, In xa la -> In xb lb -> In y l ->
  (Fa * f xa y)%pred m -> (Fb * f xb y)%pred m -> (xa = xb)) ->
  (F1 * listmatch f la l)%pred m -> (F2 * listmatch f lb l)%pred m ->
  la = lb.
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Theorem xform_listpred : forall V (l : list V) prd,
  crash_xform (listpred prd l) <=p=> listpred (fun x => crash_xform (prd x)) l.
(* hint proof tokens: 37 *)
Proof.
  induction l; simpl; intros; split; auto; xform_dist; auto.
  rewrite IHl; auto.
  rewrite IHl; auto.
Qed.
Lemma crash_xform_pprd : forall A B (prd : A -> B -> rawpred),
  (fun p => crash_xform (pprd prd p)) =
  (pprd (fun x y => crash_xform (prd x y))).
(* hint proof tokens: 34 *)
Proof.
  unfold pprd, prod_curry, crash_xform; intros.
  apply functional_extensionality; intros; destruct x; auto.
Qed.
Theorem xform_listmatch : forall A B (a : list A) (b : list B) prd,
  crash_xform (listmatch prd a b) <=p=> listmatch (fun x y => crash_xform (prd x y)) a b.
(* hint proof tokens: 37 *)
Proof.
  unfold listmatch; intros; split; xform_norm;
  rewrite xform_listpred; cancel;
  rewrite crash_xform_pprd; auto.
Qed.
Theorem xform_listpred_idem_l : forall V (l : list V) prd,
  (forall e, crash_xform (prd e) =p=> prd e) ->
  crash_xform (listpred prd l) =p=> listpred prd l.
(* hint proof tokens: 31 *)
Proof.
  induction l; simpl; intros; auto.
  xform_dist.
  rewrite H.
  rewrite IHl; auto.
Qed.
Theorem xform_listpred_idem_r : forall V (l : list V) prd,
  (forall e,  prd e =p=> crash_xform (prd e)) ->
  listpred prd l =p=> crash_xform (listpred prd l).
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Theorem xform_listpred_idem : forall V (l : list V) prd,
  (forall e, crash_xform (prd e) <=p=> prd e) ->
  crash_xform (listpred prd l) <=p=> listpred prd l.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Theorem xform_listmatch_idem_l : forall A B (a : list A) (b : list B) prd,
  (forall a b, crash_xform (prd a b) =p=> prd a b) ->
  crash_xform (listmatch prd a b) =p=> listmatch prd a b.
(* hint proof tokens: 40 *)
Proof.
  unfold listmatch; intros.
  xform_norm; cancel.
  apply xform_listpred_idem_l; intros.
  destruct e; cbn; auto.
Qed.
Theorem xform_listmatch_idem_r : forall A B (a : list A) (b : list B) prd,
  (forall a b,  prd a b =p=> crash_xform (prd a b)) ->
  listmatch prd a b =p=> crash_xform (listmatch prd a b).
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Theorem xform_listmatch_idem : forall A B (a : list A) (b : list B) prd,
  (forall a b, crash_xform (prd a b) <=p=> prd a b) ->
  crash_xform (listmatch prd a b) <=p=> listmatch prd a b.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma xform_listpred_ptsto : forall l,
  crash_xform (listpred (fun a => a |->?) l) =p=>
               listpred (fun a => a |->?) l.
(* hint proof tokens: 41 *)
Proof.
  induction l; simpl.
  rewrite crash_invariant_emp; auto.
  xform_dist.
  rewrite crash_xform_ptsto_exis, IHl.
  auto.
Qed.
Lemma xform_listpred_ptsto_fp : forall FP,
  (forall a, crash_xform (exists v, a |-> v * [[ FP v ]]) =p=> exists v, a |-> v * [[ FP v ]]) ->
  forall l,
  crash_xform (listpred (fun a => exists v, a |-> v * [[ FP v ]]) l) =p=>
               listpred (fun a => exists v, a |-> v * [[ FP v ]]) l.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma xform_listmatch_ptsto : forall al vl,
  crash_xform (listmatch (fun v a => a |-> v) vl al) =p=>
    exists l, [[ possible_crash_list vl l ]] *
    listmatch (fun v a => a |-> v) (synced_list l) al.
(* hint proof tokens: 207 *)
Proof.
  unfold listmatch; induction al; destruct vl; xform_norm.
  - cancel. instantiate (1 := nil); simpl; auto.
    unfold possible_crash_list; intuition; inversion H.
    rewrite synced_list_length; auto.
  - inversion H0.
  - inversion H0.
  - rewrite crash_xform_ptsto.
    specialize (IHal vl).
    rewrite crash_xform_sep_star_dist, crash_xform_lift_empty in IHal.
    inversion H; subst.
    setoid_rewrite lift_impl with (Q := length vl = length al) at 6; intros; eauto.
    rewrite IHal; simpl.

    cancel.
    eassign (v' :: l); cancel.
    simpl; cancel.
    apply possible_crash_list_cons; simpl; auto.
    rewrite synced_list_length in *; simpl; lia.
    apply possible_crash_list_cons; simpl; auto.
    rewrite synced_list_length in *; simpl; lia.
Qed.
Theorem sync_invariant_listpred : forall T prd (l : list T),
  (forall x, sync_invariant (prd x)) ->
  sync_invariant (listpred prd l).
(* hint proof tokens: 14 *)
Proof.
  induction l; simpl; eauto.
Qed.
Hint Resolve sync_invariant_listpred.
Theorem sync_xform_listpred : forall V (l : list V) prd,
  sync_xform (listpred prd l) <=p=> listpred (fun x => sync_xform (prd x)) l.
Proof.
(* original proof tokens: 63 *)

(* No more tactics to try *)
Admitted.

Lemma sync_xform_listpred' : forall T (l : list T) p q,
  (forall x, sync_xform (p x) =p=> q x) ->
  sync_xform (listpred p l) =p=> listpred q l.
(* hint proof tokens: 46 *)
Proof.
  induction l; simpl; intros; auto.
  apply sync_xform_emp.
  repeat rewrite sync_xform_sep_star_dist.
  rewrite IHl by eauto.
  rewrite H; auto.
Qed.
