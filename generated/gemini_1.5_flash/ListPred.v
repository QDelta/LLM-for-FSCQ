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
Proof.
(* original proof tokens: 16 *)
(* generated proof tokens: 10 *)

reflexivity.
Qed.

Theorem listpred_fwd : forall l i def, 
    i < length l ->
      listpred l =p=> listpred (firstn i l) * (prd (selN l i def)) * listpred (skipn (S i) l).
Proof.
(* original proof tokens: 34 *)
intros.
induction l; simpl.
inversion H.
auto.
destruct i; simpl.
(* No more tactics to try *)
Admitted.

Theorem listpred_bwd : forall l i def, 
    i < length l ->
      listpred (firstn i l) * (prd (selN l i def)) * listpred (skipn (S i) l) =p=> listpred l.
Proof.
(* original proof tokens: 70 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_extract : forall l i def,
    i < length l ->
    listpred l =p=> exists F, F * prd (selN l i def).
Proof.
(* original proof tokens: 27 *)
eapply pimpl_exists_l; [intros|].
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros; eapply pimpl_exists_l; intros; eapply pimpl_exists_l; intros; eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros.
eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros.
eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros.
eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros; eapply pimpl_exists_l; clear; intros.
(* Reached max number of model calls *)
Admitted.

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
(* generated proof tokens: 17 *)

intros.
rewrite H.
apply piff_refl.
Qed.

Definition sep_star_fold : (T -> @pred AT AEQ V -> @pred AT AEQ V) := fun x => sep_star (prd x).
Definition listpred' := fold_right sep_star_fold emp.
Theorem listpred_listpred': forall l,
    listpred l = listpred' l.
Proof.
(* original proof tokens: 27 *)
(* generated proof tokens: 14 *)

induction l; simpl; auto.
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
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_isolate : forall l i def,
    i < length l ->
    listpred l <=p=> listpred (removeN l i) * prd (selN l i def).
Proof.
(* original proof tokens: 60 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_split : forall l n,
    listpred l <=p=> listpred (firstn n l) * listpred (skipn n l).
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_isolate_fwd : forall l i def,
    i < length l ->
    listpred l =p=> listpred (removeN l i) * prd (selN l i def).
Proof.
(* original proof tokens: 19 *)
(* generated proof tokens: 13 *)

eapply listpred_isolate.
Qed.

Theorem listpred_updN : forall l i v,
    i < length l ->
    listpred (updN l i v) <=p=> listpred (removeN l i) * prd v.
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_updN_selN: forall l i v def,
    i < length l ->
    prd (selN l i def) =p=> prd v ->
    listpred l =p=> listpred (updN l i v).
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_nodup : forall l m,
    (forall x y : T, {x = y} + {x <> y}) ->
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    listpred l m -> NoDup l.
Proof.
(* original proof tokens: 169 *)
intros l m Hdec Hnodup Hl.
induction l; auto.
(* No more tactics to try *)
Admitted.

Theorem listpred_nodup_piff : forall l,
    (forall x y : T, {x = y} + {x <> y}) ->
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    listpred l <=p=> [[ NoDup l ]] * listpred l.
Proof.
(* original proof tokens: 32 *)
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Theorem listpred_nodup_F : forall l m,
    (forall x y : T, {x = y} + {x <> y}) ->
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    (exists F, F * listpred l)%pred m -> NoDup l.
Proof.
(* original proof tokens: 44 *)
intros.
eapply listpred_nodup; eauto.
(* No more tactics to try *)
Admitted.

Lemma listpred_permutation: forall a b,
    Permutation a b ->
    listpred a <=p=> listpred b.
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_remove :
    forall (dec : forall x y : T, {x = y} + {x <> y}) x l,
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    In x l ->
    listpred l =p=> prd x * listpred (remove dec x l).
Proof.
(* original proof tokens: 72 *)
eapply pimpl_exists_l; [ | eauto ]; intros.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_r; eauto.
eexists.
eapply pimpl_exists_l; [ | eauto ]; intros.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; intros; eauto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; [ | eauto ]; intros.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; [ | eauto ]; intros.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; [ | eauto ]; intros.
eapply pimpl_exists_r; eauto.
eapply pimpl_exists_l; [| eauto].
eapply pimpl_exists_l; [ | eauto ].
eapply pimpl_exists_l; [ | eauto ].
eapply pimpl_exists_l; [ | eauto ]; intros.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; [ | eauto ]; intros.
eapply pimpl_exists_l; eauto.
(* Reached max number of model calls *)
Admitted.

Theorem listpred_remove' :
    forall (dec : forall x y : T, {x = y} + {x <> y}) x l,
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    NoDup l ->
    In x l ->
    prd x * listpred (remove dec x l) =p=> listpred l.
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_remove_piff :
    forall (dec : forall x y : T, {x = y} + {x <> y}) x l,
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    NoDup l ->
    In x l ->
    listpred l <=p=> prd x * listpred (remove dec x l).
Proof.
(* original proof tokens: 30 *)
eapply piff_trans.
(* No more tactics to try *)
Admitted.

Theorem listpred_eq : forall l m1 m2,
    (forall x ma mb, prd x ma -> prd x mb -> ma = mb) ->
    listpred l m1 -> listpred l m2 -> m1 = m2.
Proof.
(* original proof tokens: 85 *)
intros l m1 m2 H H0 H1.
(* No more tactics to try *)
Admitted.

Theorem listpred_emp : forall l,
    (forall x, In x l -> prd x =p=> emp) ->
    listpred l =p=> emp.
Proof.
(* original proof tokens: 46 *)
intros l H.
(* No more tactics to try *)
Admitted.

Theorem listpred_emp_piff : forall l,
    (forall x, In x l -> prd x <=p=> emp) ->
    listpred l <=p=> emp.
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Lemma listpred_partition: forall f (l : list T),
    let p := partition f l in
    listpred l <=p=> listpred (fst p) * listpred (snd p).
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Lemma listpred_rev: forall l,
    listpred l <=p=> listpred (rev l).
Proof.
(* original proof tokens: 37 *)
induction l; simpl; auto.
(* No more tactics to try *)
Admitted.

End LISTPRED.
Theorem listpred_lift : forall T l AT AEQ V prd F G,
  (forall x, In x l -> prd x <=p=> [[ F x ]] * G x) ->
  @listpred T AT AEQ V prd l <=p=> [[ Forall F l ]] * listpred G l.
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_unify : forall T l1 l2 AT AEQ V f F1 F2 m,
    (forall Fa Fb a b, In a l1 -> In b l2 -> (Fa * f a)%pred m -> (Fb * f b)%pred m -> a = b) ->
    (F1 * @listpred T AT AEQ V f l1)%pred m -> (F2 * listpred f l2)%pred m ->
    length l1 = length l2 ->
    l1 = l2.
Proof.
(* original proof tokens: 138 *)
intros T l1 l2 AT AEQ V f F1 F2 m H H0 H1 H2.
(* No more tactics to try *)
Admitted.

Lemma listpred_pimpl_replace: forall T AT V M (l : list T) (F G : T -> @pred AT M V),
       (forall x, In x l -> F x =p=> G x) ->
       listpred F l =p=> listpred G l.
Proof.
(* original proof tokens: 29 *)
eapply pimpl_pimpl_proper2; auto.
eapply pimpl_pimpl_proper2; auto.
eapply pimpl_pimpl_proper1; auto.
apply pimpl_refl.
eapply pimpl_pimpl_proper2; auto.
eapply pimpl_pimpl_proper2; auto.
eapply pimpl_pimpl_proper1; auto.
eapply pimpl_refl; auto.
eapply pimpl_pimpl_proper1; auto.
(* Reached max number of model calls *)
Admitted.

Lemma listpred_piff_replace : forall A B AT M l F G,
  (forall x, In x l -> F x <=p=> G x) -> @listpred A B AT M F l <=p=> listpred G l.
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Lemma listpred_ptsto_notindomain : forall AT AEQ V (t : list AT) x (m : @Mem.mem _ AEQ V),
  listpred (fun a => (a |->?)%pred) t m ->
  ~In x t ->
  notindomain x m.
Proof.
(* original proof tokens: 84 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 22 *)
intros.
eapply pimpl_apply; eauto.
auto.
eapply pimpl_apply; eauto.
(* No more tactics to try *)
Admitted.

Lemma listmatch_length_r : forall F a b m,
    (F * listmatch a b)%pred m -> length a = length b.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_length_l : forall F a b m,
    (listmatch a b * F)%pred m -> length a = length b.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_length_pimpl : forall a b,
    listmatch a b =p=> (listmatch a b) * [[ length a = length b ]].
Proof.
(* original proof tokens: 14 *)
eapply pimpl_and_dup; eauto.
eapply pimpl_and_dup;eauto.
eapply pimpl_and_dup;eauto.
eapply pimpl_and_dup;eauto.
eapply pimpl_and_dup; eauto.
unfold listmatch; simpl; autorewrite with core; auto.
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
Proof.
(* original proof tokens: 48 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_app_rev : forall a1 b1 a2 b2,
    length a1 = length b1 \/ length a2 = length b2 ->
    listmatch (a1 ++ a2) (b1 ++ b2) =p=> listmatch a1 b1 * listmatch a2 b2.
Proof.
(* original proof tokens: 36 *)
intros.
destruct H.
(* No more tactics to try *)
Admitted.

Theorem listmatch_split : forall a b n,
    listmatch a b <=p=> listmatch (firstn n a) (firstn n b) * listmatch (skipn n a) (skipn n b).
Proof.
(* original proof tokens: 103 *)
eapply piff_trans.
apply piff_refl.
(* No more tactics to try *)
Admitted.

Theorem listmatch_emp : forall l1 l2,
    (forall x y, In x l1 -> In y l2 -> prd x y =p=> emp) ->
    listmatch l1 l2 =p=> emp.
Proof.
(* original proof tokens: 58 *)

(* No more tactics to try *)
Admitted.

Theorem listmatch_emp_piff : forall l1 l2,
    (forall x y, In x l1 -> In y l2 -> prd x y <=p=> emp) ->
    listmatch l1 l2 <=p=> [[ length l1 = length l2 ]].
Proof.
(* original proof tokens: 83 *)

(* No more tactics to try *)
Admitted.

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
split; intros; simpl in *; try (apply listmatch_repeat_r; assumption).
(* No more tactics to try *)
Admitted.

Lemma listpred_exis_listmatch: forall (a : list A),
    listpred (fun a => exists b, prd a b) a =p=> exists b, listmatch a b.
Proof.
(* original proof tokens: 53 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_rev: forall a b,
    listmatch a b <=p=> listmatch (rev a) (rev b).
Proof.
(* original proof tokens: 41 *)
eapply piff_refl.
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
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_listpred_seq_fp : forall V FP l st n,
  length l = n ->
  Forall FP l ->
  arrayN (@ptsto _ _ V) st l =p=> listpred (fun a => exists v, a |-> v * [[ FP v ]]) (seq st n).
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_sym : forall AT AEQ V A B (al : list A) (bl : list B) f,
  (@listmatch _ _ AT AEQ V) f al bl <=p=>
  listmatch (fun b a => f a b) bl al.
Proof.
(* original proof tokens: 40 *)
eapply piff_refl.
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
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Lemma listmatch_map : forall AT AEQ V A B A' B' al bl f (fa : A -> A') (fb : B -> B'),
  (@listmatch A B AT AEQ V) (fun a b => f (fa a) (fb b)) al bl <=p=>
  (@listmatch A' B' _ _ _) f (map fa al) (map fb bl).
Proof.
(* original proof tokens: 21 *)
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Lemma listpred_map : forall AT AEQ V A B l f (g : A -> B),
  @listpred B AT AEQ V f (map g l) <=p=>
  @listpred A AT AEQ V (fun a => f (g a)) l.
Proof.
(* original proof tokens: 26 *)
eapply piff_refl.
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
Proof.
(* original proof tokens: 187 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 37 *)
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Lemma crash_xform_pprd : forall A B (prd : A -> B -> rawpred),
  (fun p => crash_xform (pprd prd p)) =
  (pprd (fun x y => crash_xform (prd x y))).
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Theorem xform_listmatch : forall A B (a : list A) (b : list B) prd,
  crash_xform (listmatch prd a b) <=p=> listmatch (fun x y => crash_xform (prd x y)) a b.
Proof.
(* original proof tokens: 37 *)
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Theorem xform_listpred_idem_l : forall V (l : list V) prd,
  (forall e, crash_xform (prd e) =p=> prd e) ->
  crash_xform (listpred prd l) =p=> listpred prd l.
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Theorem xform_listpred_idem_r : forall V (l : list V) prd,
  (forall e,  prd e =p=> crash_xform (prd e)) ->
  listpred prd l =p=> crash_xform (listpred prd l).
Proof.
(* original proof tokens: 40 *)
eapply pimpl_pimpl_proper2; auto; try apply pimpl_pimpl_proper1; auto; try apply crash_xform_pimpl_proper; auto.
eapply crash_xform_pimpl; auto.
eapply crash_xform_pimpl; auto.
eapply crash_xform_pimpl; auto.
eapply xform_listpred_idem_l; auto.
apply crash_xform_idem.
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
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

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
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Lemma xform_listpred_ptsto : forall l,
  crash_xform (listpred (fun a => a |->?) l) =p=>
               listpred (fun a => a |->?) l.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 207 *)

(* No more tactics to try *)
Admitted.

Theorem sync_invariant_listpred : forall T prd (l : list T),
  (forall x, sync_invariant (prd x)) ->
  sync_invariant (listpred prd l).
Proof.
(* original proof tokens: 14 *)

(* No more tactics to try *)
Admitted.

Hint Resolve sync_invariant_listpred.
Theorem sync_xform_listpred : forall V (l : list V) prd,
  sync_xform (listpred prd l) <=p=> listpred (fun x => sync_xform (prd x)) l.
Proof.
(* original proof tokens: 63 *)
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Lemma sync_xform_listpred' : forall T (l : list T) p q,
  (forall x, sync_xform (p x) =p=> q x) ->
  sync_xform (listpred p l) =p=> listpred q l.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

