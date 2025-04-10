Require Import Mem.
Require Import ListUtils.
Require Import List Lia Ring Word Pred PredCrash.
Require Import Prog Hoare SepAuto BasicProg.
Require Import FunctionalExtensionality.
Require Import WordAuto.
Require Import AsyncDisk.
Import PeanoNat ListNotations.
Set Implicit Arguments.
Set Default Proof Using "Type".
Section GenArray.
Variable V VP : Type.
Variable pts : addr -> V -> @pred addr addr_eq_dec VP.
Infix "|-?->" := pts (at level 35) : pred_scope.
Fixpoint arrayN (a : addr) (vs : list V) : @pred _ addr_eq_dec _ :=
    match vs with
      | nil => emp
      | v :: vs' => a |-?-> v * arrayN (S a) vs'
    end%pred.
Lemma arrayN_unify : forall (a b : list V) s,
    a = b -> arrayN s a =p=> arrayN s b.
(* hint proof tokens: 14 *)
Proof.
    intros; subst; auto.
  Qed.
Lemma arrayN_one: forall v,
      0 |-?-> v <=p=> arrayN 0 [v].
(* hint proof tokens: 12 *)
Proof.
    split; cancel.
  Qed.
Lemma isolateN_fwd' : forall vs i a (default : V),
    i < length vs
    -> arrayN a vs =p=> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
(* skipped proof tokens: 157 *)
Admitted.
Theorem isolateN_fwd : forall (default : V) a i vs,
    i < length vs
    -> arrayN a vs =p=> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Lemma isolateN_bwd' : forall vs i a (default : V),
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs)
    =p=> arrayN a vs.
Proof.
(* skipped proof tokens: 133 *)
Admitted.
Theorem isolateN_bwd : forall (default : V) a i vs,
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs)
    =p=> arrayN a vs.
(* hint proof tokens: 42 *)
Proof.
    intros.
    eapply pimpl_trans; [ | apply isolateN_bwd' ].
    2: eassumption.
    apply pimpl_refl.
  Qed.
Theorem arrayN_isolate : forall (default : V) a i vs,
    i < length vs
    -> arrayN a vs <=p=>
       arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs).
(* hint proof tokens: 31 *)
Proof.
    unfold piff; split.
    apply isolateN_fwd; auto.
    apply isolateN_bwd; auto.
  Qed.
Theorem isolate_fwd_upd : forall (v : V) a i vs,
    i < length vs
    -> arrayN a (updN vs i v) <=p=>
       arrayN a (firstn i vs)
       * (a + i) |-?-> v
       * arrayN (a + i + 1) (skipn (S i) vs).
(* hint proof tokens: 71 *)
Proof.
    intros.
    erewrite arrayN_isolate with (vs:=updN vs i v) (i:=i) (default:=v);
      autorewrite with lists; auto.
    unfold piff; split.
    cancel; autorewrite with lists; cancel.
    cancel; autorewrite with lists; cancel.
  Qed.
Theorem isolateN_bwd_upd : forall (v : V) a i vs,
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> v
       * arrayN (a + i + 1) (skipn (S i) vs)
       =p=> arrayN a (updN vs i v).
(* hint proof tokens: 85 *)
Proof.
    intros.
    erewrite <- isolateN_bwd with (vs:=updN vs i v) (i:=i) (default:=v).
    rewrite selN_updN_eq by auto.
    rewrite firstn_updN_oob by auto.
    rewrite skipN_updN' by auto.
    cancel.
    rewrite length_updN.
    auto.
  Qed.
Theorem arrayN_app : forall (a b : list V) st,
    arrayN st (a ++ b) <=p=>
    arrayN st a * arrayN (st + length a) b.
(* hint proof tokens: 99 *)
Proof.
    induction a; split; simpl; auto.
    rewrite Nat.add_0_r; cancel.
    rewrite Nat.add_0_r; cancel.
    rewrite IHa.
    replace (S st + length a0) with (st + S (length a0)) by lia.
    cancel.
    rewrite IHa.
    replace (S st + length a0) with (st + S (length a0)) by lia.
    cancel.
  Qed.
Theorem arrayN_split : forall i (a : list V) st,
    arrayN st a <=p=>
    arrayN st (firstn i a) * arrayN (st + i) (skipn i a).
Proof.
(* skipped proof tokens: 165 *)
Admitted.
Lemma arrayN_ptsto_selN_0 : forall l (def : V) a,
    length l = 1 ->
    arrayN a l <=p=> (a |-?-> selN l 0 def)%pred.
(* hint proof tokens: 48 *)
Proof.
    destruct l; simpl; intros; try congruence.
    assert (length l = 0) by lia.
    apply length_nil in H0; subst; simpl; split; cancel.
  Qed.
Lemma arrayN_isolate_hd : forall l (def : V) a,
    length l >= 1 ->
    arrayN a l <=p=> (a |-?-> selN l 0 def * arrayN (a + 1) (skipn 1 l) )%pred.
Proof.
(* skipped proof tokens: 36 *)
Admitted.
End GenArray.
Section PtstoArray.
Variable V : Type.
Notation pts := (@ptsto addr addr_eq_dec V).
Lemma arrayN_oob': forall (l : list V) a i m,
    i >= length l
    -> arrayN pts a l m
    -> m (a + i) = None.
Proof.
(* skipped proof tokens: 150 *)
Admitted.
Lemma arrayN_oob: forall (l : list V) i m,
    i >= length l
    -> arrayN pts 0 l m
    -> m i = None.
(* hint proof tokens: 33 *)
Proof.
    intros.
    replace i with (0 + i) by lia.
    eapply arrayN_oob'; eauto.
  Qed.
Lemma arrayN_oob_lt: forall (l : list V) i a m,
    arrayN pts a l m ->
    i < a ->
    m i = None.
(* hint proof tokens: 78 *)
Proof.
    induction l; intros; auto; simpl in *.
    unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H.
    repeat deex.
    unfold mem_union.
    unfold ptsto in H2; destruct H2; rewrite H2.
    eapply IHl; eauto.
    lia.
  Qed.
Lemma arrayN_updN_memupd : forall F l a i (v : V) m,
    (F * arrayN pts a l)%pred m ->
    i < length l ->
    (F * arrayN pts a (updN l i v))%pred (Mem.upd m (a + i) v).
Proof.
(* skipped proof tokens: 117 *)
Admitted.
Lemma arrayN_app_memupd : forall l (v : V) m,
    arrayN pts 0 l m
    -> arrayN pts 0 (l ++ v :: nil) (Mem.upd m (length l) v).
(* hint proof tokens: 114 *)
Proof.
    intros.

    eapply isolateN_bwd with (i := (length l)) (default := v).
    rewrite app_length; simpl; lia.

    rewrite firstn_app2; auto.
    rewrite selN_last; auto.
    rewrite skipn_oob; [ | rewrite app_length; simpl; lia ].
    unfold arrayN at 2; auto; apply emp_star_r.
    simpl.

    apply ptsto_upd_disjoint; auto.
    eapply arrayN_oob; eauto.
  Qed.
Theorem arrayN_list_eq : forall (vs1 vs2 : list V) s m,
    arrayN pts s vs1 m -> arrayN pts s vs2 m -> vs1 = vs2.
Proof.
(* skipped proof tokens: 118 *)
Admitted.
Theorem arrayN_strictly_exact : forall (vs : list V) base,
    strictly_exact (arrayN pts base vs).
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma arrayN_selN : forall F a st l m (def : V),
    (F * arrayN pts st l)%pred m ->
    a >= st ->
    a < st + length l ->
    m a = Some (selN l (a - st) def).
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Lemma arrayN_selN_exis : forall F a st (l : list V) m,
    (F * arrayN pts st l)%pred m ->
    a >= st ->
    a < st + length l ->
    exists v, m a = Some v.
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_unify' : forall a b s m (F1 F2 : pred), length a = length b ->
    (F1 * arrayN pts s a)%pred m -> (F2 * arrayN pts s b)%pred m -> a = b.
Proof.
(* skipped proof tokens: 238 *)
Admitted.
End PtstoArray.
Lemma arrayN_piff_replace: forall T V (l : list T) n (p q : _ -> _ -> @pred _ _ V),
  (forall i d x, i < length l -> selN l i d = x -> p (i + n) x <=p=> q (i + n) x) ->
  arrayN p n l <=p=> arrayN q n l.
Proof.
(* skipped proof tokens: 65 *)
Admitted.
Lemma arrayN_map: forall V T T' (l : list T) n (p : addr -> T' -> @pred _ _ V) (f : T -> T'),
  arrayN p n (map f l) <=p=> arrayN (fun i x => p i (f x)) n l.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Definition vsupd (vs : list valuset) (i : addr) (v : valu) : list valuset :=
  updN vs i (v, vsmerge (selN vs i ($0, nil))).
Definition vssync (vs : list valuset) (i : addr) : list valuset :=
  updN vs i (fst (selN vs i ($0, nil)), nil).
Definition vsupd_range (vsl : list valuset) (vl : list valu) :=
  let n := length vl in
  (List.combine vl (map vsmerge (firstn n vsl))) ++ skipn n vsl.
Definition vs_synced a (vl : list valuset) :=
  snd (selN vl a ($0, nil)) = nil.
Lemma vsupd_length : forall vsl a v,
  length (vsupd vsl a v) = length vsl.
(* hint proof tokens: 21 *)
Proof.
  unfold vsupd; intros.
  rewrite length_updN; auto.
Qed.
Lemma vsupd_range_length : forall vsl l,
  length l <= length vsl ->
  length (vsupd_range vsl l) = length vsl.
(* hint proof tokens: 52 *)
Proof.
  unfold vsupd_range; intros.
  rewrite app_length.
  rewrite combine_length.
  rewrite Nat.min_l.
  rewrite skipn_length.
  lia.
  rewrite map_length.
  rewrite firstn_length_l; auto.
Qed.
Lemma vsupd_range_nil : forall vsl,
  vsupd_range vsl nil = vsl.
(* hint proof tokens: 23 *)
Proof.
  unfold vsupd_range; intros.
  autorewrite with lists; simpl; auto.
Qed.
Lemma vsupd_range_progress : forall i vsl l,
  length l <= length vsl -> i < length l ->
    (vsupd (vsupd_range vsl (firstn i l)) i (selN l i $0))
  = (vsupd_range vsl ((firstn i l) ++ [ selN l i $0 ])).
Proof.
(* skipped proof tokens: 261 *)
Admitted.
Lemma forall_incl_refl : forall vs,
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) vs vs.
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Lemma vsupd_range_incl : forall l vs,
  length l <= length vs ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) vs (vsupd_range vs l).
(* hint proof tokens: 66 *)
Proof.
  induction l; intros; simpl.
  rewrite vsupd_range_nil.
  apply forall_incl_refl.

  destruct vs.
  inversion H.
  cbn.
  constructor.
  apply incl_tl; apply incl_refl.
  apply IHl.
  simpl in *; lia.
Qed.
Lemma vsupd_range_selN_oob : forall vs n l,
  n >= length l ->
  length l <= length vs ->
  selN (vsupd_range vs l) n ($0, nil) = selN vs n ($0, nil).
Proof.
(* skipped proof tokens: 71 *)
Admitted.
Lemma vsupd_range_selN_inb : forall vs n l,
  n < length l ->
  length l <= length vs ->
  selN (vsupd_range vs l) n ($0, nil) = (selN l n $0, vsmerge (selN vs n ($0, nil))).
Proof.
(* skipped proof tokens: 84 *)
Admitted.
Lemma vsupd_range_firstn_incl : forall n l vs,
  length l <= length vs ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) 
            (vsupd_range vs (firstn n l)) (vsupd_range vs l).
Proof.
(* original proof tokens: 157 *)
induction n; intros.
(* No more tactics to try *)
Admitted.

Definition vssync_range (vsl : list valuset) n :=
  (List.combine (map fst (firstn n vsl)) (repeat nil n)) ++ skipn n vsl.
Lemma vssync_range_length : forall vsl n,
  n <= length vsl ->
  length (vssync_range vsl n) = length vsl.
Proof.
(* skipped proof tokens: 67 *)
Admitted.
Lemma vssync_range_progress : forall vs m,
  m < length vs ->
  vssync (vssync_range vs m) m = vssync_range vs (S m).
(* hint proof tokens: 229 *)
Proof.
  unfold vssync, vssync_range; intros.
  rewrite updN_app2.
  erewrite firstn_S_selN by auto.
  rewrite map_app.
  rewrite repeat_app_tail.
  rewrite combine_app
    by (autorewrite with lists; rewrite firstn_length_l; lia).
  rewrite <- app_assoc; f_equal.
  rewrite combine_length; autorewrite with lists.
  rewrite Nat.min_l; repeat rewrite firstn_length_l; try lia.
  replace (m - m) with 0 by lia.
  rewrite updN_0_skip_1 by (rewrite skipn_length; lia).
  rewrite skipn_skipn; simpl.
  f_equal; f_equal.
  rewrite selN_app2.
  rewrite combine_length; rewrite Nat.min_l;
     autorewrite with lists; repeat rewrite firstn_length_l; try lia.
  replace (m + (m - m)) with m by lia.
  unfold vsmerge; auto.
  all: rewrite combine_length_eq2; autorewrite with lists;
    repeat rewrite firstn_length_l; lia.
Qed.
Lemma vssync_range_incl : forall n vs,
  n <= length vs ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) (vssync_range vs n) vs.
Proof.
(* skipped proof tokens: 194 *)
Admitted.
Definition vsupsyn_range (vsl : list valuset) (vl : list valu) :=
  let n := length vl in
  (List.combine vl (repeat nil n)) ++ skipn n vsl.
Lemma vsupsyn_range_length : forall vsl l,
  length l <= length vsl ->
  length (vsupsyn_range vsl l) = length vsl.
(* hint proof tokens: 46 *)
Proof.
  unfold vsupsyn_range; intros.
  rewrite app_length.
  rewrite combine_length.
  rewrite Nat.min_l.
  rewrite skipn_length.
  lia.
  rewrite repeat_length; auto.
Qed.
Lemma vsupsyn_range_selN : forall vsl vl i def,
  i < length vl ->
  selN (vsupsyn_range vsl vl) i (def, nil) = (selN vl i def, nil).
(* hint proof tokens: 56 *)
Proof.
  unfold vsupsyn_range; intros.
  rewrite selN_app1.
  rewrite selN_combine, repeat_selN; auto.
  rewrite repeat_length; auto.
  rewrite combine_length_eq; auto.
  rewrite repeat_length; auto.
Qed.
Lemma vsupsyn_range_selN_oob : forall vsl vl i def,
  i >= length vl ->
  selN (vsupsyn_range vsl vl) i def = selN vsl i def.
(* hint proof tokens: 66 *)
Proof.
  unfold vsupsyn_range; intros.
  rewrite selN_app2.
  rewrite skipn_selN.
  rewrite combine_length_eq.
  rewrite Minus.le_plus_minus_r; auto.
  rewrite repeat_length; auto.
  rewrite combine_length_eq; auto.
  rewrite repeat_length; auto.
Qed.
Lemma vsupd_range_app_tl : forall l vs v,
  length l + 1 <= length vs ->
  vsupd_range vs (l ++ [v]) = vsupd (vsupd_range vs l) (length l) v.
(* hint proof tokens: 154 *)
Proof.
  unfold vsupd_range, vsupd; intros.
  rewrite updN_app2, selN_app2; rewrite combine_length, map_length, firstn_length, Nat.min_l; auto;
  try apply Nat.min_case_strong; intros; try lia.
  rewrite Nat.sub_diag, app_length; simpl.
  erewrite firstn_plusone_selN, map_app by lia.
  rewrite combine_app by (rewrite map_length, firstn_length_l by lia; auto); simpl.
  rewrite app_assoc_reverse, updN_0_skip_1, <- cons_app by (rewrite skipn_length; lia).
  rewrite skipn_skipn', skipn_selN, Nat.add_0_r.
  reflexivity.
Qed.
Definition vsupd_vecs (vsl : list valuset) (l : list (addr * valu)) : list valuset :=
  fold_left (fun vs e => (vsupd vs (fst e) (snd e))) l vsl.
Lemma vsupd_vecs_length : forall l vs,
  length (vsupd_vecs vs l) = length vs.
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma vsupd_vecs_length_ok : forall l m def vs,
  Forall (fun e => fst e < length vs) l ->
  m < length l ->
  fst (selN l m def) < length (vsupd_vecs vs (firstn m l)).
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_progress : forall l m vs,
  m < length l ->
  let e := selN l m (0, $0) in
  vsupd (vsupd_vecs vs (firstn m l)) (fst e) (snd e) =
  vsupd_vecs vs (firstn (S m) l).
(* hint proof tokens: 39 *)
Proof.
  induction l; intros.
  inversion H.
  destruct m; auto.
  simpl.
  rewrite IHl; auto.
  simpl in H.
  lia.
Qed.
Lemma vsupd_comm : forall l a1 v1 a2 v2,
  a1 <> a2 ->
  vsupd (vsupd l a1 v1) a2 v2 = vsupd (vsupd l a2 v2) a1 v1.
Proof.
(* skipped proof tokens: 32 *)
Admitted.
Lemma vsupd_vecs_vsupd_notin : forall av l a v,
  ~ In a (map fst av) ->
  vsupd_vecs (vsupd l a v) av = vsupd (vsupd_vecs l av) a v.
Proof.
(* original proof tokens: 41 *)
induction av; intros.
(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_selN_not_in : forall l a d,
  ~ In a (map fst l) ->
  selN (vsupd_vecs d l) a ($0, nil) = selN d a ($0, nil).
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma vsupd_vecs_app : forall d a b,
  vsupd_vecs d (a ++ b) = vsupd_vecs (vsupd_vecs d a) b.
(* hint proof tokens: 22 *)
Proof.
  unfold vsupd_vecs; intros.
  rewrite fold_left_app; auto.
Qed.
Lemma vsupd_vecs_cons : forall l a v avl,
  vsupd_vecs l ((a, v) :: avl) = vsupd_vecs (vsupd l a v) avl.
Proof.
(* skipped proof tokens: 8 *)
Admitted.
Lemma vsupd_vecs_selN_vsmerge_in' : forall a v avl l,
  In v (vsmerge (selN l a ($0, nil))) ->
  a < length l ->
  In v (vsmerge (selN (vsupd_vecs l avl) a ($0, nil))).
Proof.
(* skipped proof tokens: 264 *)
Admitted.
Lemma vsupd_vecs_selN_vsmerge_in : forall a v avl l,
  In v (vsmerge (selN l a ($0, nil))) ->
  In v (vsmerge (selN (vsupd_vecs l avl) a ($0, nil))).
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Lemma vsupd_vecs_incl : forall l vs,
  Forall (fun e => fst e < length vs) l ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) vs (vsupd_vecs vs l).
(* hint proof tokens: 51 *)
Proof.
  intros.
  eapply selN_Forall2.
  rewrite vsupd_vecs_length; auto.
  intros.
  unfold incl; intros.
  apply vsupd_vecs_selN_vsmerge_in; eauto.
Qed.
Lemma vsupd_vecs_firstn_incl : forall n l vs,
  Forall (fun e => fst e < length vs) l ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) 
            (vsupd_vecs vs (firstn n l)) (vsupd_vecs vs l).
Proof.
(* skipped proof tokens: 197 *)
Admitted.
Definition vssync_vecs (vsl : list valuset) (l : list addr) : list valuset :=
  fold_left vssync l vsl.
Definition vssync_vecs_rev (vsl : list valuset) (l : list addr) : list valuset :=
  fold_right (fun a m => vssync m a) vsl (rev l).
Theorem vssync_vecs_rev_eq : forall l vsl,
  vssync_vecs vsl l = vssync_vecs_rev vsl l.
(* hint proof tokens: 31 *)
Proof.
  intros; unfold vssync_vecs, vssync_vecs_rev.
  rewrite fold_left_rev_right; auto.
Qed.
Lemma vssync_vecs_app : forall m l a,
  vssync_vecs m (l ++ [a]) = vssync (vssync_vecs m l) a.
(* hint proof tokens: 36 *)
Proof.
  intros.
  repeat rewrite vssync_vecs_rev_eq.
  unfold vssync_vecs_rev.
  rewrite rev_unit; reflexivity.
Qed.
Lemma vssync_vecs_length : forall l vs,
  length (vssync_vecs vs l) = length vs.
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Lemma vssync_vecs_length_ok : forall l m def vs,
  Forall (fun e => e < length vs) l ->
  m < length l ->
  selN l m def < length (vssync_vecs vs (firstn m l)).
Proof.
(* skipped proof tokens: 38 *)
Admitted.
Lemma vssync_vecs_progress : forall l m vs,
  m < length l ->
  vssync (vssync_vecs vs (firstn m l)) (selN l m 0) =
  vssync_vecs vs (firstn (S m) l).
(* hint proof tokens: 39 *)
Proof.
  induction l; intros.
  inversion H.
  destruct m; auto.
  simpl.
  rewrite IHl; auto.
  simpl in H.
  lia.
Qed.
Lemma vssync_vecs_cons: forall a d x,
  vssync_vecs d (x :: a) = vssync_vecs (vssync d x) a.
(* hint proof tokens: 8 *)
Proof.
  auto.
Qed.
Lemma vssync_vecs_vssync_comm : forall l d a,
  vssync_vecs (vssync d a) l = vssync (vssync_vecs d l) a.
Proof.
(* skipped proof tokens: 61 *)
Admitted.
Lemma vssync_vecs_comm: forall l l' vs,
  vssync_vecs (vssync_vecs vs l) l' = vssync_vecs (vssync_vecs vs l') l.
(* hint proof tokens: 52 *)
Proof.
  induction l; intros.
  auto.
  rewrite vssync_vecs_cons.
  rewrite IHl.
  rewrite vssync_vecs_vssync_comm.
  rewrite vssync_vecs_cons.
  auto.
Qed.
Lemma vssync_vecs_app_comm: forall l l' vs,
  vssync_vecs vs (l ++ l') = vssync_vecs vs (l' ++ l).
(* hint proof tokens: 90 *)
Proof.
  induction l; intros.
  rewrite app_nil_r.
  auto.
  rewrite <- app_comm_cons.
  rewrite vssync_vecs_cons.
  change (a :: l) with ([a] ++ l).
  rewrite app_assoc.
  rewrite <- IHl.
  rewrite app_assoc.
  rewrite vssync_vecs_app.
  rewrite vssync_vecs_vssync_comm.
  auto.
Qed.
Lemma vssync_vecs_app': forall l l' vs,
  vssync_vecs (vssync_vecs vs l) l' = vssync_vecs vs (l ++ l').
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Lemma vssync_synced : forall l a,
  vs_synced a l ->
  vssync l a = l.
(* hint proof tokens: 73 *)
Proof.
  unfold vs_synced, vssync.
  intros.
  rewrite <- H.
  destruct (Compare_dec.lt_dec a (length l)).
  erewrite selN_inb, <- surjective_pairing by auto.
  rewrite updN_selN_eq; auto.
  rewrite updN_oob by lia.
  auto.
Qed.
Lemma vs_synced_vssync_nop: forall vs a,
  vs_synced a vs -> vssync vs a = vs.
(* hint proof tokens: 50 *)
Proof.
  unfold vs_synced, vssync.
  intuition.
  eapply selN_eq_updN_eq.
  destruct selN eqn:H'; cbn in *.
  rewrite H'; congruence.
Qed.
Lemma vssync_vecs_nop: forall vs l,
  Forall (fun a => vs_synced a vs) l ->
  vssync_vecs vs l = vs.
(* hint proof tokens: 62 *)
Proof.
  induction l; intros.
  auto.
  inversion H; subst.
  rewrite vssync_vecs_cons.
  rewrite vssync_vecs_vssync_comm.
  rewrite IHl; auto.
  eapply vs_synced_vssync_nop; auto.
Qed.
Lemma vssync_vecs_nil: forall vs,
  vssync_vecs vs nil = vs.
(* hint proof tokens: 20 *)
Proof.
  intros.
  apply vssync_vecs_nop; constructor.
Qed.
Lemma vssync_comm: forall vs a b,
  vssync (vssync vs a) b = vssync (vssync vs b) a.
(* hint proof tokens: 47 *)
Proof.
  intros.
  unfold vssync.
  destruct (addr_eq_dec a b); subst; auto.
  repeat rewrite selN_updN_ne by auto.
  rewrite updN_comm; auto.
Qed.
Lemma vssync_vsupd_eq : forall l a v,
  vssync (vsupd l a v) a = updN l a (v, nil).
Proof.
(* skipped proof tokens: 78 *)
Admitted.
Lemma updN_vsupd_vecs_notin : forall av l a v,
  ~ In a (map fst av) ->
  updN (vsupd_vecs l av) a v = vsupd_vecs (updN l a v) av.
(* hint proof tokens: 59 *)
Proof.
  induction av; simpl; intros; auto.
  destruct a; simpl in *; intuition.
  rewrite IHav by auto.
  unfold vsupd, vsmerge.
  rewrite updN_comm by auto.
  rewrite selN_updN_ne; auto.
Qed.
Lemma vssync_selN_not_in : forall l i d,
  ~ In i l ->
  selN (vssync_vecs d l) i ($0, nil) = selN d i ($0, nil).
Proof.
(* skipped proof tokens: 41 *)
Admitted.
Lemma vssync_vecs_selN_In : forall l i d,
  In i l ->
  i < length d ->
  selN (vssync_vecs d l) i ($0, nil) = (fst (selN d i ($0, nil)), nil).
(* hint proof tokens: 148 *)
Proof.
  induction l; intros; auto.
  inversion H.
  destruct (addr_eq_dec a i); subst; simpl.
  destruct (in_dec addr_eq_dec i l).
  rewrite IHl; unfold vssync; auto.
  rewrite selN_updN_eq; simpl; auto.
  rewrite length_updN; auto.

  rewrite vssync_selN_not_in by auto.
  unfold vssync; rewrite selN_updN_eq; simpl; auto.

  inversion H; subst; try congruence.
  rewrite IHl; unfold vssync; auto.
  rewrite selN_updN_ne; auto.
  rewrite length_updN; auto.
Qed.
Lemma vssync_vecs_incl : forall l vs,
  Forall (fun a => a < length vs) l ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) (vssync_vecs vs l) vs.
Proof.
(* skipped proof tokens: 167 *)
Admitted.
Definition synced_list m: list valuset := List.combine m (repeat nil (length m)).
Definition possible_crash_list (l: list valuset) (l': list valu) :=
  length l = length l' /\
  forall i, i < length l -> In (selN l' i $0) (vsmerge (selN l i ($0, nil))).
Lemma synced_list_selN : forall l i def,
  selN (synced_list l) i (def, nil) = (selN l i def, nil).
Proof.
(* skipped proof tokens: 69 *)
Admitted.
Lemma synced_list_map_fst : forall l,
  map fst (synced_list l) = l.
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Lemma synced_list_map_fst_map : forall (vsl : list valuset),
  synced_list (map fst vsl) = map (fun x => (fst x, nil)) vsl.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma vsupsyn_range_synced_list : forall a b,
  length a = length b ->
  vsupsyn_range a b = synced_list b.
(* hint proof tokens: 34 *)
Proof.
  unfold vsupsyn_range, synced_list; intros.
  rewrite skipn_oob by lia.
  rewrite app_nil_r; auto.
Qed.
Lemma possible_crash_list_length : forall l l',
  possible_crash_list l l' -> length l = length l'.
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Lemma synced_list_length : forall l,
  length (synced_list l) = length l.
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Lemma synced_list_updN : forall l a v,
  updN (synced_list l) a (v, nil) = synced_list (updN l a v).
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Lemma synced_list_app : forall a b,
  synced_list (a ++ b) = synced_list a ++ synced_list b.
(* hint proof tokens: 34 *)
Proof.
  induction a; simpl; auto; intros.
  unfold synced_list at 1; simpl.
  f_equal.
  apply IHa.
Qed.
Lemma synced_list_inj : forall a b, synced_list a = synced_list b -> a = b.
Proof.
(* skipped proof tokens: 83 *)
Admitted.
Lemma map_snd_synced_list_eq : forall a b,
  length a = length b ->
  map snd (synced_list a) = map snd (synced_list b).
(* hint proof tokens: 28 *)
Proof.
  unfold synced_list; intros.
  repeat rewrite map_snd_combine; autorewrite with lists; auto.
Qed.
Lemma map_snd_vsupd_vecs_not_in : forall l d a v,
  ~ In a (map fst l) ->
  NoDup (map fst l) ->
  map snd (vsupd_vecs (synced_list (updN d a v)) l) = map snd (vsupd_vecs (synced_list d) l).
(* hint proof tokens: 140 *)
Proof.
  induction l; simpl; intros.
  erewrite map_snd_synced_list_eq; eauto.
  autorewrite with lists; auto.

  destruct a; intuition; simpl in *.
  inversion H0; subst.
  setoid_rewrite vsupd_vecs_vsupd_notin; auto.
  unfold vsupd.
  repeat rewrite map_snd_updN.
  f_equal.
  apply IHl; auto.
  f_equal; f_equal; f_equal.
  rewrite <- synced_list_updN.
  rewrite <- updN_vsupd_vecs_notin by auto.
  rewrite selN_updN_ne; auto.
Qed.
Lemma possible_crash_list_updN : forall l l' a v vs,
  possible_crash_list l l' ->
  possible_crash_list (updN l a (v, vs)) (updN l' a v).
(* hint proof tokens: 64 *)
Proof.
  unfold possible_crash_list; simpl; intuition;
  autorewrite with lists in *; auto.
  destruct (Nat.eq_dec a i); subst.
  repeat rewrite selN_updN_eq; auto; lia.
  repeat rewrite selN_updN_ne; eauto.
Qed.
Lemma possible_crash_list_unique : forall a b,
  (forall n, snd (selN a n ($0, nil)) = nil) ->
  possible_crash_list a b ->
  b = map fst a.
Proof.
(* skipped proof tokens: 78 *)
Admitted.
Lemma possible_crash_list_synced_list_eq : forall a b,
  possible_crash_list (synced_list a) b -> a = b.
(* hint proof tokens: 117 *)
Proof.
  unfold possible_crash_list; intuition.
  rewrite synced_list_length in *.
  eapply list_selN_ext; auto; intros.
  specialize (H1 _ H).
  inversion H1.

  generalize H2.
  unfold synced_list; rewrite selN_combine; eauto.
  rewrite repeat_length; auto.

  generalize H2.
  unfold synced_list; rewrite selN_combine; simpl.
  rewrite repeat_selN by auto.
  intro Hx; inversion Hx.
  rewrite repeat_length; auto.
Qed.
Lemma possible_crash_list_synced_list : forall l,
  possible_crash_list (synced_list l) l.
(* hint proof tokens: 45 *)
Proof.
  unfold possible_crash_list; intuition.
  rewrite synced_list_length; auto.
  unfold synced_list; constructor.
  rewrite selN_combine; auto.
  rewrite repeat_length; auto.
Qed.
Lemma possible_crash_list_cons : forall vsl vl v vs,
  possible_crash_list vsl vl ->
  In v (vsmerge vs) ->
  possible_crash_list (vs :: vsl) (v :: vl).
(* hint proof tokens: 39 *)
Proof.
  unfold possible_crash_list; intuition.
  simpl; lia.
  destruct i, vs, vsl; try now firstorder; eauto with arith.
Qed.
Theorem possible_crash_list_vssync : forall l l' a,
  possible_crash_list (vssync l a) l' ->
  possible_crash_list l l'.
Proof.
(* skipped proof tokens: 85 *)
Admitted.
Section ArrayCrashXform.
Notation pts := (@ptsto addr addr_eq_dec valuset).
Lemma crash_xform_arrayN: forall l st,
    crash_xform (arrayN pts st l) =p=>
      exists l', [[ possible_crash_list l l' ]] *
      arrayN pts st (synced_list l').
Proof.
(* original proof tokens: 93 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_arrayN_r: forall l l' st,
    possible_crash_list l' l ->
    arrayN pts st (synced_list l) =p=> crash_xform (arrayN pts st l').
Proof.
(* skipped proof tokens: 149 *)
Admitted.
Lemma crash_xform_synced_arrayN: forall l st,
    Forall (fun x => snd x = nil) l ->
    crash_xform (arrayN pts st l) =p=> arrayN pts st l.
(* hint proof tokens: 69 *)
Proof.
    induction l; simpl; auto; intros.
    xform.
    rewrite IHl.
    cancel; subst.
    inversion H; simpl in *; subst; auto.
    inversion H; simpl in *; subst.
    inversion H1.
    eapply Forall_cons2; eauto.
  Qed.
Lemma crash_xform_arrayN_combine_nils: forall (l : list valu) st,
    crash_xform (arrayN pts st (List.combine l (repeat nil (length l)))) =p=>
    arrayN pts st (List.combine l (repeat nil (length l))).
(* hint proof tokens: 51 *)
Proof.
    intros.
    apply crash_xform_synced_arrayN.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.
Lemma crash_xform_arrayN_synced: forall (l : list valu) st,
    crash_xform (arrayN pts st (synced_list l)) =p=>
    arrayN pts st (List.combine l (repeat nil (length l))).
(* hint proof tokens: 51 *)
Proof.
    intros.
    apply crash_xform_synced_arrayN.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.
End ArrayCrashXform.
Section SubsetArray.
Theorem sync_invariant_arrayN_subset : forall vs a,
    sync_invariant (arrayN ptsto_subset a vs).
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Lemma arrayN_subset_oob': forall l a i m,
    i >= length l
    -> arrayN ptsto_subset a l m
    -> m (a + i) = None.
(* hint proof tokens: 192 *)
Proof.
    induction l; intros; auto; simpl in *.
    destruct (Peano_dec.eq_nat_dec i 0); auto.
    subst; simpl in *; lia.

    unfold sep_star in H0; rewrite sep_star_is in H0; unfold sep_star_impl in H0.
    repeat deex.
    unfold mem_union.
    unfold ptsto_subset in H2.
    destruct_lift H2.
    unfold ptsto in H1; destruct H1.
    pose proof (IHl (S a0) (i - 1)).
    replace (S a0 + (i - 1)) with (a0 + i) in H3 by lia.
    destruct (m1 (a0 + i)) eqn:?.
    contradict Heqo.
    rewrite H2; try congruence.
    lia.
    apply H3.
    lia.
    auto.
  Qed.
Lemma arrayN_subset_oob: forall l i m,
    i >= length l
    -> arrayN ptsto_subset 0 l m
    -> m i = None.
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma arrayN_selN_subset : forall F a st l m def,
    (F * arrayN ptsto_subset st l)%pred m ->
    a >= st ->
    a < st + length l ->
    let vs0 := (selN l (a - st) def) in
    exists vs, m a = Some vs /\ fst vs = fst vs0 /\ incl (snd vs) (snd vs0).
(* hint proof tokens: 96 *)
Proof.
    cbn; intros.
    rewrite arrayN_isolate with (i := a - st) in H by lia.
    unfold ptsto_subset at 2 in H; destruct_lift H; simpl in *.
    eexists; split; try split.
    eapply ptsto_valid.
    pred_apply; replace (st + (a - st)) with a by lia; cancel.
    simpl; auto.
    auto.
  Qed.
Lemma arrayN_subset_memupd : forall F l a i v vs vs' m,
    (F * arrayN ptsto_subset a l)%pred m ->
    incl vs' vs ->
    i < length l ->
    (F * arrayN ptsto_subset a (updN l i (v, vs)))%pred (Mem.upd m (a + i) (v, vs')).
Proof.
(* skipped proof tokens: 170 *)
Admitted.
Lemma crash_xform_arrayN_subset: forall l st,
    crash_xform (arrayN ptsto_subset st l) =p=>
      exists l', [[ possible_crash_list l l' ]] *
      arrayN ptsto_subset st (synced_list l').
Proof.
(* skipped proof tokens: 110 *)
Admitted.
Lemma crash_xform_arrayN_subset_r: forall l l' st,
    possible_crash_list l' l ->
    arrayN ptsto_subset st (synced_list l) =p=>
     crash_xform (arrayN ptsto_subset st l').
(* hint proof tokens: 160 *)
Proof.
    unfold possible_crash_list.
    induction l; simpl; intros; auto.
    - intuition; destruct l'; simpl in *; try congruence.
      apply crash_invariant_emp_r.
    - intuition; destruct l'; simpl in *; try congruence.
      pose proof (H1 0) as H1'. simpl in H1'.
      rewrite IHl.
      rewrite crash_xform_sep_star_dist.
      rewrite <- crash_xform_ptsto_subset_r with (v := a) by (apply H1'; lia).
      rewrite ptsto_subset_pimpl_ptsto.
      apply pimpl_refl.
      intuition.
      specialize (H1 (S i)). simpl in H1. apply H1. lia.
  Qed.
Hint Resolve incl_refl.
Lemma crash_xform_synced_arrayN_subset: forall l st,
    Forall (fun x => snd x = nil) l ->
    crash_xform (arrayN ptsto_subset st l) =p=> arrayN ptsto_subset st l.
(* hint proof tokens: 86 *)
Proof.
    induction l; simpl; auto; intros.
    xform.
    rewrite IHl.
    cancel; subst.
    rewrite crash_xform_ptsto_subset; unfold ptsto_subset.
    cancel.
    inversion H; simpl in *; subst; auto.
    inversion H; simpl in *; subst.
    inversion H0.
    eapply Forall_cons2; eauto.
  Qed.
Lemma crash_xform_arrayN_subset_combine_nils: forall (l : list valu) st,
    crash_xform (arrayN ptsto_subset st (List.combine l (repeat nil (length l)))) =p=>
    arrayN ptsto_subset st (List.combine l (repeat nil (length l))).
(* hint proof tokens: 52 *)
Proof.
    intros.
    apply crash_xform_synced_arrayN_subset.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.
Lemma crash_xform_arrayN_subset_synced: forall (l : list valu) st,
    crash_xform (arrayN ptsto_subset st (synced_list l)) =p=>
    arrayN ptsto_subset st (List.combine l (repeat nil (length l))).
Proof.
(* original proof tokens: 52 *)
(* generated proof tokens: 57 *)

intros.
apply crash_xform_synced_arrayN_subset.
rewrite Forall_forall; intros.
induction l; simpl in *; auto.
inversion H; subst; simpl; auto.
inversion H; subst; simpl; auto.
Qed.

End SubsetArray.
Hint Resolve sync_invariant_arrayN_subset.
Notation arrayS := (arrayN ptsto_subset).
Section ListUpd.
Variable V : Type.
Notation pts := (@ptsto addr addr_eq_dec V).
Fixpoint listupd (m : @mem _ addr_eq_dec V) base (vs : list V) :=
    match vs with
    | nil => m
    | v :: tl => listupd (upd m base v) (S base) tl
    end.
Lemma arrayN_listupd: forall l (m : @mem _ _ V) l0 base F,
    (F * arrayN pts base l0 )%pred m ->
    length l0 = length l ->
    (F * arrayN pts base l)%pred (listupd m base l).
(* hint proof tokens: 80 *)
Proof.
    induction l; intros; destruct l0; simpl in *; auto; try lia.
    apply sep_star_assoc.
    eapply IHl with (l0 := l0); eauto.
    setoid_rewrite sep_star_comm at 1.
    apply sep_star_assoc.
    eapply ptsto_upd.
    pred_apply; cancel.
  Qed.
Lemma arrayN_listupd_eq : forall (l : list V) F st d,
    (F * arrayN pts st l)%pred d ->
    d = listupd d st l.
(* hint proof tokens: 72 *)
Proof.
    induction l; simpl; intros; auto.
    erewrite <- IHl.
    rewrite upd_nop; auto.
    eapply ptsto_valid.
    pred_apply; cancel.
    rewrite upd_nop; auto.
    pred_apply; cancel.
    eapply ptsto_valid.
    pred_apply; cancel.
  Qed.
Lemma listupd_sel_oob : forall (l : list V) a off m,
    a < off \/ a >= off + (length l) ->
    listupd m off l a = m a.
Proof.
(* skipped proof tokens: 55 *)
Admitted.
Lemma listupd_sel_inb : forall (l : list V) a off m def,
    a >= off ->
    a < off + (length l) ->
    listupd m off l a = Some (selN l (a - off) def).
Proof.
(* skipped proof tokens: 84 *)
Admitted.
Lemma listupd_sel_cases : forall (l : list V) a off m def,
    ((a < off \/ a >= off + (length l)) /\ listupd m off l a = m a ) \/
    (a >= off /\ a < off + (length l) /\ listupd m off l a = Some (selN l (a - off) def) ).
Proof.
(* skipped proof tokens: 66 *)
Admitted.
End ListUpd.
Section ListUpdSubset.
Lemma arrayN_listupd_subset : forall l m l0 base F,
    (F * arrayN ptsto_subset base l0 )%pred m ->
    length l0 = length l ->
    (F * arrayN ptsto_subset base l)%pred (listupd m base l).
(* hint proof tokens: 98 *)
Proof.
    induction l; intros; destruct l0; simpl in *; auto; try lia.
    apply sep_star_assoc.
    eapply IHl with (l0 := l0); eauto.
    setoid_rewrite sep_star_comm at 1.
    apply sep_star_assoc.
    apply sep_star_comm; destruct a, p.
    eapply ptsto_subset_upd.
    pred_apply; cancel.
    apply incl_refl.
  Qed.
End ListUpdSubset.
