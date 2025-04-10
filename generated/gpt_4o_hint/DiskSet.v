Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import List.
Require Import ListUtils.
Require Import Word.
Require Import Array.
Require Import LogReplay.
Require Import NEList.
Require Import AsyncDisk.
Require Import LogReplay.
Require Import DiskLogHash.
Require Import Pred.
Require Import Morphisms.
Require Import GenSepN.
Import ListNotations.
Import LogReplay.
Set Implicit Arguments.
Definition diskset  := nelist diskstate.
Definition dsupd (ds : diskset) a v := 
  d_map (fun x => updN x a v) ds.
Definition dssync (ds : diskset) a := 
  d_map (fun x => vssync x a) ds.
Definition dsupd_vecs (ds : diskset) av := 
  d_map (fun x => vsupd_vecs x av) ds.
Definition dssync_vecs (ds : diskset) al := 
  d_map (fun x => vssync_vecs x al) ds.
Definition ds_synced a (ds : diskset) :=
  Forall (vs_synced a) (fst ds :: snd ds).
Lemma dsupd_latest : forall ds a v,
  latest (dsupd ds a v) = updN (latest ds) a v.
(* hint proof tokens: 20 *)
Proof.
  unfold dsupd; intros.
  rewrite d_map_latest; auto.
Qed.
Lemma dsupd_fst : forall ds a v,
  fst (dsupd ds a v) = updN (fst ds) a v.
(* hint proof tokens: 21 *)
Proof.
  unfold dsupd; intros.
  rewrite d_map_fst; auto.
Qed.
Lemma dsupd_nthd : forall ds a v n,
  nthd n (dsupd ds a v) = updN (nthd n ds) a v.
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Lemma dssync_latest : forall ds a,
  latest (dssync ds a) = vssync (latest ds) a.
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Lemma dssync_nthd : forall ds a n,
  nthd n (dssync ds a) = vssync (nthd n ds) a.
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Lemma dsupd_vecs_latest : forall ds avl,
  latest (dsupd_vecs ds avl) = vsupd_vecs (latest ds) avl.
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Lemma dsupd_vecs_nthd : forall ds avl n,
  nthd n (dsupd_vecs ds avl) = vsupd_vecs (nthd n ds) avl.
(* hint proof tokens: 24 *)
Proof.
  unfold dsupd_vecs; intros.
  rewrite d_map_nthd; auto.
Qed.
Lemma dsupd_vecs_fst : forall ds avl,
  fst (dsupd_vecs ds avl) = vsupd_vecs (fst ds) avl.
(* hint proof tokens: 19 *)
Proof.
  unfold dsupd_vecs; intros.
  simpl; auto.
Qed.
Lemma dssync_vecs_latest : forall ds al,
  latest (dssync_vecs ds al) = vssync_vecs (latest ds) al.
(* hint proof tokens: 23 *)
Proof.
  unfold dssync_vecs; intros.
  rewrite d_map_latest; auto.
Qed.
Lemma dssync_vecs_nthd : forall ds al n,
  nthd n (dssync_vecs ds al) = vssync_vecs (nthd n ds) al.
(* hint proof tokens: 25 *)
Proof.
  unfold dssync_vecs; intros.
  rewrite d_map_nthd; auto.
Qed.
Lemma dssync_latest_length : forall ds a,
  length (latest (dssync ds a)) = length (latest ds).
(* hint proof tokens: 28 *)
Proof.
  intros; rewrite dssync_latest.
  unfold vssync; rewrite length_updN; auto.
Qed.
Lemma dsupd_latest_length : forall ds a v,
  length (latest (dsupd ds a v)) = length (latest ds).
(* hint proof tokens: 22 *)
Proof.
  intros; rewrite dsupd_latest.
  rewrite length_updN; auto.
Qed.
Lemma dsupd_vecs_latest_length : forall ds avl,
  length (latest (dsupd_vecs ds avl)) = length (latest ds).
(* hint proof tokens: 25 *)
Proof.
  intros; rewrite dsupd_vecs_latest.
  rewrite vsupd_vecs_length; auto.
Qed.
Lemma dssync_vecs_latest_length : forall ds al,
  length (latest (dssync_vecs ds al)) = length (latest ds).
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Lemma nthd_cons_inb : forall T d0 ds (d : T) n,
  n <= length ds ->
  nthd n (d0, d :: ds) = nthd n (d0, ds).
Proof.
(* skipped proof tokens: 60 *)
Admitted.
Lemma dssync_vecs_nop: forall vs l,
  Forall (fun a => ds_synced a vs) l ->
  dssync_vecs vs l = vs.
(* hint proof tokens: 159 *)
Proof.
  unfold dssync_vecs, d_map.
  intros.
  destruct vs; cbn; f_equal.
  eapply vssync_vecs_nop.
  rewrite Forall_forall in *.
  intuition.
  unfold ds_synced in *.
  specialize (H x); intuition.
  inversion H1; auto.
  rewrite <- map_id.
  eapply map_ext_in.
  rewrite Forall_forall in *.
  unfold ds_synced in *.
  intuition; cbn in *.
  eapply vssync_vecs_nop.
  rewrite Forall_forall.
  intros x; specialize (H x); intuition.
  rewrite Forall_forall in *.
  cbn in *; intuition.
Qed.
Lemma dssync_comm: forall d a b,
  dssync (dssync d a) b = dssync (dssync d b) a.
(* hint proof tokens: 66 *)
Proof.
  unfold dssync, d_map.
  destruct d; cbn -[vssync]; intros.
  f_equal.
  rewrite vssync_comm.
  auto.
  repeat rewrite map_map.
  eapply map_ext_in; intros.
  rewrite vssync_comm; auto.
Qed.
Lemma dssync_vecs_cons: forall l vs x,
  dssync_vecs vs (x :: l) = dssync_vecs (dssync vs x) l.
(* hint proof tokens: 47 *)
Proof.
  unfold dssync_vecs, dssync.
  intros.
  cbn.
  destruct vs; unfold d_map; cbn.
  f_equal.
  rewrite map_map.
  auto.
Qed.
Lemma dssync_vecs_dssync_comm: forall l x vs,
  dssync_vecs (dssync vs x) l = dssync (dssync_vecs vs l) x.
Proof.
(* skipped proof tokens: 55 *)
Admitted.
Lemma dssync_vecs_app: forall vs l l',
  dssync_vecs vs (l ++ l') = dssync_vecs (dssync_vecs vs l) l'.
(* hint proof tokens: 58 *)
Proof.
  induction l; cbn.
  rewrite dssync_vecs_nop; auto.
  constructor.
  intros.
  repeat rewrite dssync_vecs_cons.
  repeat rewrite dssync_vecs_dssync_comm.
  congruence.
Qed.
Lemma dssync_vecs_permutation: forall ds l l',
  Permutation.Permutation l l' ->
  dssync_vecs ds l = dssync_vecs ds l'.
Proof.
(* skipped proof tokens: 72 *)
Admitted.
Definition txnlist  := list DLog.contents.
Module ReplaySeq.
Inductive ReplaySeq : diskset -> txnlist -> Prop :=
    | RSeqNil  : forall d0, ReplaySeq (d0, nil) nil
    | RSeqCons : forall d0 d t ds ts,
          d = replay_disk t (hd d0 ds) ->
          ReplaySeq (d0, ds) ts -> 
          ReplaySeq (d0, (d :: ds)) (t :: ts).
Lemma replay_seq_length : forall ds ts,
    ReplaySeq ds ts -> length (snd ds) = length ts.
Proof.
(* skipped proof tokens: 17 *)
Admitted.
Lemma repaly_seq_latest : forall ds ts,
    ReplaySeq ds ts ->
    latest ds = fold_right replay_disk (fst ds) ts.
Proof.
(* original proof tokens: 31 *)
(* generated proof tokens: 34 *)

intros ds ts H.
induction H.
- simpl. reflexivity.
- simpl in *. rewrite <- IHReplaySeq. assumption.
Qed.

Lemma replay_seq_selN : forall n ds ts,
    ReplaySeq ds ts ->
    n < length (snd ds) ->
    selN (snd ds) n (fst ds) = fold_right replay_disk (fst ds) (skipn n ts).
(* hint proof tokens: 85 *)
Proof.
    induction n; simpl; intros; auto.
    destruct ds.
    apply repaly_seq_latest in H; rewrite <- H.
    destruct l; intuition.
    pose proof (replay_seq_length H).
    inversion H; auto; subst; simpl in *.
    specialize (IHn (d0, ds0)).
    apply IHn; simpl; auto; lia.
  Qed.
Lemma replay_seq_nthd : forall n ds ts,
    ReplaySeq ds ts ->
    nthd n ds = fold_right replay_disk (fst ds) (skipn (length ts - n) ts).
(* hint proof tokens: 120 *)
Proof.
    unfold nthd; intros.
    destruct n; simpl.
    rewrite selN_oob, skipn_oob by lia; auto.
    erewrite <- replay_seq_length by eauto.
    destruct (lt_dec (length (snd ds)) (S n)).
    replace (length (snd ds) - S n) with 0 by lia; simpl.
    rewrite <- repaly_seq_latest by auto.
    unfold latest; destruct ds; simpl.
    destruct l0; firstorder.
    apply replay_seq_selN; auto; lia.
  Qed.
Lemma fold_right_replay_disk_length : forall l d,
    length (fold_right replay_disk d l) = length d.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma replay_seq_latest_length : forall ds ts,
    ReplaySeq ds ts ->
    length (latest ds) = length (fst ds).
(* hint proof tokens: 32 *)
Proof.
    intros.
    erewrite repaly_seq_latest; eauto.
    rewrite fold_right_replay_disk_length; auto.
  Qed.
Lemma replay_seq_nthd_length : forall ds ts n,
    ReplaySeq ds ts ->
    length (nthd n ds) = length (fst ds).
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Lemma replay_seq_dsupd_notin : forall ds ts a v,
    ReplaySeq ds ts ->
    Forall (fun e => ~ In a (map fst e)) ts ->
    ReplaySeq (dsupd ds a v) ts.
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Local Hint Resolve ents_remove_not_in.
Lemma replay_seq_dsupd_ents_remove : forall ds ts a v,
    ReplaySeq ds ts ->
    ReplaySeq (dsupd ds a v) (map (ents_remove a) ts).
Proof.
(* skipped proof tokens: 73 *)
Admitted.
Lemma replay_seq_dssync_notin : forall ds ts a,
    ReplaySeq ds ts ->
    ReplaySeq (dssync ds a) ts.
Proof.
(* original proof tokens: 62 *)

(* No more tactics to try *)
Admitted.

Lemma replay_seq_dsupd_vecs_disjoint : forall ds ts avl,
    ReplaySeq ds ts ->
    Forall (fun e => disjoint (map fst avl) (map fst e)) ts ->
    ReplaySeq (dsupd_vecs ds avl) ts.
Proof.
(* skipped proof tokens: 61 *)
Admitted.
Lemma replay_seq_dssync_vecs_disjoint : forall ds ts al,
    ReplaySeq ds ts ->
    Forall (fun e => disjoint al (map fst e)) ts ->
    ReplaySeq (dssync_vecs ds al) ts.
Proof.
(* skipped proof tokens: 62 *)
Admitted.
Lemma replay_seq_dssync_vecs_ents : forall ds ts al,
    ReplaySeq ds ts ->
    ReplaySeq (dssync_vecs ds al) ts.
Proof.
(* skipped proof tokens: 67 *)
Admitted.
End ReplaySeq.
Definition diskset_pred  V (p : @pred _ _ V) ds :=
  forall d, d_in d ds -> p (list2nmem d).
Instance diskset_pred_pimpl_eq_impl {V} :
  Proper (pimpl ==> eq ==> Basics.impl) (@diskset_pred V).
(* hint proof tokens: 32 *)
Proof.
  intros p p' Hp ds ds' Hds Hpd.
  unfold diskset_pred in *; subst; eauto.
Qed.
Instance diskset_pred_flip_pimpl_eq_flip_impl {V} :
  Proper (Basics.flip pimpl ==> eq ==> Basics.flip Basics.impl) (@diskset_pred V).
(* hint proof tokens: 32 *)
Proof.
  intros p p' Hp ds ds' Hds Hpd.
  unfold diskset_pred in *; subst; eauto.
Qed.
Instance diskset_pred_piff_eq_impl {V} :
  Proper (piff ==> eq ==> Basics.impl) (@diskset_pred V).
(* hint proof tokens: 36 *)
Proof.
  intros p p' Hp ds ds' Hds Hpd.
  inversion Hp.
  unfold diskset_pred in *; subst; eauto.
Qed.
Instance diskset_pred_piff_eq_flip_impl {V} :
  Proper (piff ==> eq ==> Basics.flip Basics.impl) (@diskset_pred V).
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Lemma diskset_pred_d_map : forall V (p1 p2 : @pred _ _ V) f ds,
  diskset_pred p1 ds ->
  (forall d, p1 (list2nmem d) -> p2 (list2nmem (f d))) ->
  diskset_pred p2 (d_map f ds).
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Export NEList.
