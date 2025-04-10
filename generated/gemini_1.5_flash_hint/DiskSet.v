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
Proof.
(* original proof tokens: 20 *)

(* No more tactics to try *)
Admitted.

Lemma dsupd_fst : forall ds a v,
  fst (dsupd ds a v) = updN (fst ds) a v.
Proof.
(* original proof tokens: 21 *)
(* generated proof tokens: 18 *)

unfold dsupd, d_map; simpl; auto.
Qed.

Lemma dsupd_nthd : forall ds a v n,
  nthd n (dsupd ds a v) = updN (nthd n ds) a v.
(* hint proof tokens: 22 *)
Proof.
  unfold dsupd; intros.
  rewrite d_map_nthd; auto.
Qed.
Lemma dssync_latest : forall ds a,
  latest (dssync ds a) = vssync (latest ds) a.
(* hint proof tokens: 21 *)
Proof.
  unfold dssync; intros.
  rewrite d_map_latest; auto.
Qed.
Lemma dssync_nthd : forall ds a n,
  nthd n (dssync ds a) = vssync (nthd n ds) a.
(* hint proof tokens: 23 *)
Proof.
  unfold dssync; intros.
  rewrite d_map_nthd; auto.
Qed.
Lemma dsupd_vecs_latest : forall ds avl,
  latest (dsupd_vecs ds avl) = vsupd_vecs (latest ds) avl.
(* hint proof tokens: 22 *)
Proof.
  unfold dsupd_vecs; intros.
  rewrite d_map_latest; auto.
Qed.
Lemma dsupd_vecs_nthd : forall ds avl n,
  nthd n (dsupd_vecs ds avl) = vsupd_vecs (nthd n ds) avl.
Proof.
(* original proof tokens: 24 *)
(* generated proof tokens: 24 *)

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
Proof.
(* original proof tokens: 23 *)
unfold dssync_vecs, latest; auto.
(* No more tactics to try *)
Admitted.

Lemma dssync_vecs_nthd : forall ds al n,
  nthd n (dssync_vecs ds al) = vssync_vecs (nthd n ds) al.
(* hint proof tokens: 25 *)
Proof.
  unfold dssync_vecs; intros.
  rewrite d_map_nthd; auto.
Qed.
Lemma dssync_latest_length : forall ds a,
  length (latest (dssync ds a)) = length (latest ds).
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma dsupd_latest_length : forall ds a v,
  length (latest (dsupd ds a v)) = length (latest ds).
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma dsupd_vecs_latest_length : forall ds avl,
  length (latest (dsupd_vecs ds avl)) = length (latest ds).
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Lemma dssync_vecs_latest_length : forall ds al,
  length (latest (dssync_vecs ds al)) = length (latest ds).
(* hint proof tokens: 27 *)
Proof.
  intros; rewrite dssync_vecs_latest.
  rewrite vssync_vecs_length; auto.
Qed.
Lemma nthd_cons_inb : forall T d0 ds (d : T) n,
  n <= length ds ->
  nthd n (d0, d :: ds) = nthd n (d0, ds).
Proof.
(* original proof tokens: 60 *)
unfold nthd; intros; simpl.
destruct n; simpl; try lia.
rewrite Nat.sub_0_r.
reflexivity.
(* No more tactics to try *)
Admitted.

Lemma dssync_vecs_nop: forall vs l,
  Forall (fun a => ds_synced a vs) l ->
  dssync_vecs vs l = vs.
Proof.
(* original proof tokens: 159 *)

(* No more tactics to try *)
Admitted.

Lemma dssync_comm: forall d a b,
  dssync (dssync d a) b = dssync (dssync d b) a.
Proof.
(* original proof tokens: 66 *)
unfold dssync; intros.
(* No more tactics to try *)
Admitted.

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
(* original proof tokens: 55 *)
unfold dssync_vecs, dssync; intros.
(* No more tactics to try *)
Admitted.

Lemma dssync_vecs_app: forall vs l l',
  dssync_vecs vs (l ++ l') = dssync_vecs (dssync_vecs vs l) l'.
Proof.
(* original proof tokens: 58 *)
unfold dssync_vecs.
(* No more tactics to try *)
Admitted.

Lemma dssync_vecs_permutation: forall ds l l',
  Permutation.Permutation l l' ->
  dssync_vecs ds l = dssync_vecs ds l'.
Proof.
(* original proof tokens: 72 *)

(* No more tactics to try *)
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
(* hint proof tokens: 17 *)
Proof.
    induction 1; simpl; firstorder.
  Qed.
Lemma repaly_seq_latest : forall ds ts,
    ReplaySeq ds ts ->
    latest ds = fold_right replay_disk (fst ds) ts.
(* hint proof tokens: 31 *)
Proof.
    induction 1; simpl in *; intros; firstorder.
    rewrite <- IHReplaySeq; firstorder.
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
Proof.
(* original proof tokens: 120 *)

(* No more tactics to try *)
Admitted.

Lemma fold_right_replay_disk_length : forall l d,
    length (fold_right replay_disk d l) = length d.
(* hint proof tokens: 25 *)
Proof.
    induction l; simpl; auto; intros.
    rewrite replay_disk_length; auto.
  Qed.
Lemma replay_seq_latest_length : forall ds ts,
    ReplaySeq ds ts ->
    length (latest ds) = length (fst ds).
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma replay_seq_nthd_length : forall ds ts n,
    ReplaySeq ds ts ->
    length (nthd n ds) = length (fst ds).
(* hint proof tokens: 33 *)
Proof.
    intros.
    erewrite replay_seq_nthd; eauto.
    rewrite fold_right_replay_disk_length; auto.
  Qed.
Lemma replay_seq_dsupd_notin : forall ds ts a v,
    ReplaySeq ds ts ->
    Forall (fun e => ~ In a (map fst e)) ts ->
    ReplaySeq (dsupd ds a v) ts.
(* hint proof tokens: 63 *)
Proof.
    induction 1; intros.
    constructor.
    inversion H1; subst.
    unfold dsupd, d_map; simpl.
    constructor.
    rewrite <- replay_disk_updN_comm by auto.
    destruct ds; auto.
    apply IHReplaySeq; auto.
  Qed.
Local Hint Resolve ents_remove_not_in.
Lemma replay_seq_dsupd_ents_remove : forall ds ts a v,
    ReplaySeq ds ts ->
    ReplaySeq (dsupd ds a v) (map (ents_remove a) ts).
Proof.
(* original proof tokens: 73 *)

(* No more tactics to try *)
Admitted.

Lemma replay_seq_dssync_notin : forall ds ts a,
    ReplaySeq ds ts ->
    ReplaySeq (dssync ds a) ts.
(* hint proof tokens: 62 *)
Proof.
    induction 1; intros.
    constructor.
    unfold dssync, d_map; simpl.
    constructor.
    2: apply IHReplaySeq; auto.
    destruct ds; subst; simpl;
    rewrite replay_disk_vssync_comm_list; auto.
  Qed.
Lemma replay_seq_dsupd_vecs_disjoint : forall ds ts avl,
    ReplaySeq ds ts ->
    Forall (fun e => disjoint (map fst avl) (map fst e)) ts ->
    ReplaySeq (dsupd_vecs ds avl) ts.
(* hint proof tokens: 61 *)
Proof.
    induction 1; intros.
    constructor.
    inversion H1; subst.
    unfold dsupd_vecs, d_map; simpl.
    constructor; auto.
    rewrite replay_disk_vsupd_vecs_disjoint by auto.
    destruct ds; auto.
  Qed.
Lemma replay_seq_dssync_vecs_disjoint : forall ds ts al,
    ReplaySeq ds ts ->
    Forall (fun e => disjoint al (map fst e)) ts ->
    ReplaySeq (dssync_vecs ds al) ts.
(* hint proof tokens: 62 *)
Proof.
    induction 1; intros.
    constructor.
    inversion H1; subst.
    unfold dssync_vecs, d_map; simpl.
    constructor; auto.
    rewrite replay_disk_vssync_vecs_disjoint by auto.
    destruct ds; auto.
  Qed.
Lemma replay_seq_dssync_vecs_ents : forall ds ts al,
    ReplaySeq ds ts ->
    ReplaySeq (dssync_vecs ds al) ts.
(* hint proof tokens: 67 *)
Proof.
    induction 1; simpl; subst.
    constructor.
    unfold dssync_vecs, d_map; simpl.
    constructor.
    2: apply IHReplaySeq; auto.
    destruct ds; simpl;
    rewrite <- replay_disk_vssync_vecs_comm_list; auto.
  Qed.
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
Proof.
(* original proof tokens: 36 *)
intros p q Hp ds ds' Hds.
unfold diskset_pred in *.
subst.
eauto.
intros.
unfold diskset_pred in *.
unfold piff in Hp.
destruct Hp.
intuition.
auto.
(* No more tactics to try *)
Admitted.

Instance diskset_pred_piff_eq_flip_impl {V} :
  Proper (piff ==> eq ==> Basics.flip Basics.impl) (@diskset_pred V).
Proof.
(* original proof tokens: 36 *)
unfold Proper, diskset_pred, Basics.impl, piff; intros.
(* No more tactics to try *)
Admitted.

Lemma diskset_pred_d_map : forall V (p1 p2 : @pred _ _ V) f ds,
  diskset_pred p1 ds ->
  (forall d, p1 (list2nmem d) -> p2 (list2nmem (f d))) ->
  diskset_pred p2 (d_map f ds).
Proof.
(* original proof tokens: 30 *)
unfold diskset_pred; intros.
eapply d_in_d_map in H1; destruct H1 as (d' & H1 & H2).
(* No more tactics to try *)
Admitted.

Export NEList.
