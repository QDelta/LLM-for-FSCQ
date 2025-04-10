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

(* No more tactics to try *)
Admitted.

Lemma dsupd_nthd : forall ds a v n,
  nthd n (dsupd ds a v) = updN (nthd n ds) a v.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma dssync_latest : forall ds a,
  latest (dssync ds a) = vssync (latest ds) a.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma dssync_nthd : forall ds a n,
  nthd n (dssync ds a) = vssync (nthd n ds) a.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma dsupd_vecs_latest : forall ds avl,
  latest (dsupd_vecs ds avl) = vsupd_vecs (latest ds) avl.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma dsupd_vecs_nthd : forall ds avl n,
  nthd n (dsupd_vecs ds avl) = vsupd_vecs (nthd n ds) avl.
Proof.
(* original proof tokens: 24 *)
simpl; induction ds as [v' ds' IH]; destruct n; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma dsupd_vecs_fst : forall ds avl,
  fst (dsupd_vecs ds avl) = vsupd_vecs (fst ds) avl.
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Lemma dssync_vecs_latest : forall ds al,
  latest (dssync_vecs ds al) = vssync_vecs (latest ds) al.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma dssync_vecs_nthd : forall ds al n,
  nthd n (dssync_vecs ds al) = vssync_vecs (nthd n ds) al.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Lemma nthd_cons_inb : forall T d0 ds (d : T) n,
  n <= length ds ->
  nthd n (d0, d :: ds) = nthd n (d0, ds).
Proof.
(* original proof tokens: 60 *)

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

(* No more tactics to try *)
Admitted.

Lemma dssync_vecs_cons: forall l vs x,
  dssync_vecs vs (x :: l) = dssync_vecs (dssync vs x) l.
Proof.
(* original proof tokens: 47 *)

(* No more tactics to try *)
Admitted.

Lemma dssync_vecs_dssync_comm: forall l x vs,
  dssync_vecs (dssync vs x) l = dssync (dssync_vecs vs l) x.
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Lemma dssync_vecs_app: forall vs l l',
  dssync_vecs vs (l ++ l') = dssync_vecs (dssync_vecs vs l) l'.
Proof.
(* original proof tokens: 58 *)

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
Proof.
(* original proof tokens: 17 *)
(* generated proof tokens: 15 *)

induction 1; simpl; auto.
Qed.

Lemma repaly_seq_latest : forall ds ts,
    ReplaySeq ds ts ->
    latest ds = fold_right replay_disk (fst ds) ts.
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Lemma replay_seq_selN : forall n ds ts,
    ReplaySeq ds ts ->
    n < length (snd ds) ->
    selN (snd ds) n (fst ds) = fold_right replay_disk (fst ds) (skipn n ts).
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Lemma replay_seq_nthd : forall n ds ts,
    ReplaySeq ds ts ->
    nthd n ds = fold_right replay_disk (fst ds) (skipn (length ts - n) ts).
Proof.
(* original proof tokens: 120 *)

(* No more tactics to try *)
Admitted.

Lemma fold_right_replay_disk_length : forall l d,
    length (fold_right replay_disk d l) = length d.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma replay_seq_dsupd_notin : forall ds ts a v,
    ReplaySeq ds ts ->
    Forall (fun e => ~ In a (map fst e)) ts ->
    ReplaySeq (dsupd ds a v) ts.
Proof.
(* original proof tokens: 63 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 62 *)

(* No more tactics to try *)
Admitted.

Lemma replay_seq_dsupd_vecs_disjoint : forall ds ts avl,
    ReplaySeq ds ts ->
    Forall (fun e => disjoint (map fst avl) (map fst e)) ts ->
    ReplaySeq (dsupd_vecs ds avl) ts.
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

Lemma replay_seq_dssync_vecs_disjoint : forall ds ts al,
    ReplaySeq ds ts ->
    Forall (fun e => disjoint al (map fst e)) ts ->
    ReplaySeq (dssync_vecs ds al) ts.
Proof.
(* original proof tokens: 62 *)

(* No more tactics to try *)
Admitted.

Lemma replay_seq_dssync_vecs_ents : forall ds ts al,
    ReplaySeq ds ts ->
    ReplaySeq (dssync_vecs ds al) ts.
Proof.
(* original proof tokens: 67 *)

(* No more tactics to try *)
Admitted.

End ReplaySeq.
Definition diskset_pred  V (p : @pred _ _ V) ds :=
  forall d, d_in d ds -> p (list2nmem d).
Instance diskset_pred_pimpl_eq_impl {V} :
  Proper (pimpl ==> eq ==> Basics.impl) (@diskset_pred V).
Proof.
(* original proof tokens: 32 *)
intro; unfold diskset_pred; intros; subst. auto.
(* No more tactics to try *)
Admitted.

Instance diskset_pred_flip_pimpl_eq_flip_impl {V} :
  Proper (Basics.flip pimpl ==> eq ==> Basics.flip Basics.impl) (@diskset_pred V).
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Instance diskset_pred_piff_eq_impl {V} :
  Proper (piff ==> eq ==> Basics.impl) (@diskset_pred V).
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Instance diskset_pred_piff_eq_flip_impl {V} :
  Proper (piff ==> eq ==> Basics.flip Basics.impl) (@diskset_pred V).
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma diskset_pred_d_map : forall V (p1 p2 : @pred _ _ V) f ds,
  diskset_pred p1 ds ->
  (forall d, p1 (list2nmem d) -> p2 (list2nmem (f d))) ->
  diskset_pred p2 (d_map f ds).
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Export NEList.
