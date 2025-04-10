Require Import BFile.
Require Import SepAuto.
Require Import Pred.
Require Import Array.
Require Import AsyncDisk.
Require Import FunctionalExtensionality.
Require Import Morphisms.
Require Import GenSepN.
Require Import Arith.
Require Import Lia.
Require Import List.
Require Import ListUtils.
Import BFILE.
Theorem file_crash_trans : forall f1 f2 f3,
  file_crash f1 f2 ->
  file_crash f2 f3 ->
  file_crash f1 f3.
Proof.
(* original proof tokens: 41 *)
intros.
destruct H as (vs1 & H1 & H2).
destruct H0 as (vs2 & H3 & H4).
eexists.
split.
(* No more tactics to try *)
Admitted.

Definition possible_fmem_crash (m m' : @Mem.mem addr addr_eq_dec BFILE.bfile) :=
  forall a,
  (m a = None /\ m' a = None) \/
  (exists f f', m a = Some f /\ m' a = Some f' /\ file_crash f f').
Definition flist_crash_xform (p : @pred addr addr_eq_dec BFILE.bfile) : @pred addr addr_eq_dec BFILE.bfile :=
  fun mf => exists mf', p mf' /\ possible_fmem_crash mf' mf.
Theorem possible_fmem_crash_mem_union : forall ma mb m', possible_fmem_crash (mem_union ma mb) m'
  -> @mem_disjoint _ addr_eq_dec _ ma mb
  -> exists ma' mb', m' = mem_union ma' mb' /\ mem_disjoint ma' mb' /\
                     possible_fmem_crash ma ma' /\ possible_fmem_crash mb mb'.
(* hint proof tokens: 396 *)
Proof.
  intros.
  exists (fun a => match ma a with | None => None | Some v => m' a end).
  exists (fun a => match mb a with | None => None | Some v => m' a end).
  repeat split.

  - unfold mem_union; apply functional_extensionality; intros.
    case_eq (ma x); case_eq (mb x); case_eq (m' x); auto.
    intros; unfold possible_fmem_crash in *.
    destruct (H x).
    destruct H4; congruence.
    repeat deex. unfold mem_union in H5.
    rewrite H2 in H5. rewrite H3 in H5. congruence.
  - unfold mem_disjoint; intro; repeat deex.
    case_eq (ma a); case_eq (mb a); intros.
    firstorder.
    rewrite H1 in H3; congruence.
    rewrite H4 in H2; congruence.
    rewrite H4 in H2; congruence.
  - unfold possible_fmem_crash in *; intro a.
    case_eq (ma a); intros; [right|left]; auto.
    pose proof (mem_union_addr a H0 H1).
    destruct (H a); destruct H3; try congruence.
    repeat deex. do 2 eexists. intuition eauto.
    congruence.
  - unfold possible_fmem_crash in *; intro a.
    case_eq (mb a); intros; [right|left]; auto.
    rewrite mem_disjoint_comm in H0.
    pose proof (mem_union_addr a H0 H1); rewrite mem_union_comm in H2 by auto.
    destruct (H a); destruct H3; try congruence.
    repeat deex. do 2 eexists. intuition eauto.
    congruence.
Qed.
Theorem possible_fmem_crash_disjoint : forall ma mb ma' mb',
  @mem_disjoint _ addr_eq_dec _ ma' mb'
  -> possible_fmem_crash ma ma'
  -> possible_fmem_crash mb mb'
  -> @mem_disjoint _ addr_eq_dec _ ma mb.
(* hint proof tokens: 67 *)
Proof.
  unfold mem_disjoint, possible_fmem_crash; intros.
  intro Hnot.
  repeat deex.
  destruct (H0 a); destruct (H1 a); try intuition congruence.
  repeat deex.
  apply H.
  do 3 eexists; eauto.
Qed.
Theorem possible_fmem_crash_union : forall ma mb ma' mb', possible_fmem_crash ma ma'
  -> possible_fmem_crash mb mb'
  -> possible_fmem_crash (mem_union ma mb) (mem_union ma' mb').
Proof.
(* original proof tokens: 180 *)

(* No more tactics to try *)
Admitted.

Lemma flist_crash_xform_sep_star : forall p q,
  flist_crash_xform (p * q) <=p=> flist_crash_xform p * flist_crash_xform q.
(* hint proof tokens: 122 *)
Proof.
  unfold_sep_star.
  unfold flist_crash_xform, piff, pimpl.
  split; intros; repeat deex.
  - edestruct possible_fmem_crash_mem_union; eauto.
    repeat deex.
    do 2 eexists. intuition eauto.
  - eexists. split.
    do 2 eexists. intuition idtac. 2: eauto. 2: eauto.
    eapply possible_fmem_crash_disjoint; eauto.
    eapply possible_fmem_crash_union; eauto.
Qed.
Lemma flist_crash_xform_ptsto : forall a f,
  flist_crash_xform (a |-> f) =p=> exists f', a |-> f' * [[ file_crash f f' ]].
(* hint proof tokens: 131 *)
Proof.
  unfold flist_crash_xform, ptsto, pimpl, possible_fmem_crash, and, lift; intros.
  repeat deex.
  specialize (H1 a) as H1a; intuition; try congruence; repeat deex.
  exists f'.
  eapply sep_star_lift_apply'.
  2: congruence.
  intuition (try congruence).
  specialize (H1 a') as H1a'; intuition; try congruence.
  repeat deex; try congruence. rewrite H2 in * by eauto. congruence.
Qed.
Lemma flist_crash_xform_lift_empty : forall P,
  flist_crash_xform [[ P ]] <=p=> [[ P ]].
(* hint proof tokens: 63 *)
Proof.
  unfold lift_empty, flist_crash_xform, possible_fmem_crash, piff, pimpl; split; intros; repeat deex.
  - specialize (H1 a); intuition; repeat deex; congruence.
  - eexists; intuition eauto.
Qed.
Lemma flist_crash_xform_emp :
  flist_crash_xform emp <=p=> emp.
Proof.
(* original proof tokens: 62 *)
split; intros; repeat deex; auto.
(* No more tactics to try *)
Admitted.

Lemma flist_crash_xform_exists : forall T p,
  flist_crash_xform (exists (x : T), p x) =p=> exists x, flist_crash_xform (p x).
Proof.
(* original proof tokens: 9 *)
unfold flist_crash_xform, pimpl, exis; intros.
eexists; eexists; intuition.
destruct H.
(* No more tactics to try *)
Admitted.

Lemma flist_crash_flist_crash_xform : forall f f' (P : @pred _ _ _),
  flist_crash f f' ->
  P (list2nmem f) ->
  (flist_crash_xform P) (list2nmem f').
(* hint proof tokens: 166 *)
Proof.
  intros; unfold flist_crash_xform, possible_fmem_crash.
  eexists; intuition eauto.
  destruct (lt_dec a (length f)).
  - right. unfold flist_crash in *.
    do 2 eexists.
    unfold list2nmem.
    erewrite selN_map by lia.
    erewrite selN_map by ( erewrite <- flist_crash_length by eauto; lia ).
    intuition eauto.
    eapply forall2_selN; auto.
  - left. unfold list2nmem. repeat rewrite selN_oob; auto; rewrite map_length.
    erewrite <- flist_crash_length by eauto. lia. lia.
Unshelve.
  all: exact BFILE.bfile0.
Qed.
Instance flist_crash_xform_pimpl_proper :
  Proper (pimpl ==> pimpl) flist_crash_xform.
Proof.
(* original proof tokens: 9 *)
unfold Proper, pimpl; intros.
intros.
eapply pimpl_trans.
2:eapply pimpl_trans.
3:eapply pimpl_trans.
4:eapply pimpl_trans.
5:eapply pimpl_trans.
6:eapply pimpl_trans.
7:eapply pimpl_trans.
8:eapply pimpl_trans.
9:eapply pimpl_trans.
10:eapply pimpl_trans.
11:eapply pimpl_trans.
12:eapply pimpl_trans.
13:eapply pimpl_trans.
14:eapply pimpl_trans.
eapply pimpl_trans.
eapply pimpl_trans.
eapply pimpl_trans.
eapply pimpl_trans; [apply flist_crash_xform_sep_star |].
apply flist_crash_xform_sep_star.
eapply flist_crash_xform_sep_star; eauto.
apply flist_crash_xform_sep_star.
eapply flist_crash_xform_sep_star; eauto.
eapply flist_crash_xform_sep_star; eauto.
eapply flist_crash_xform_sep_star; eauto.
eapply flist_crash_xform_sep_star; eauto.
eapply pimpl_refl.
eapply flist_crash_xform_sep_star; eauto.
apply flist_crash_xform_sep_star.
apply flist_crash_xform_sep_star.
apply flist_crash_xform_sep_star.
apply flist_crash_xform_sep_star.
apply flist_crash_xform_sep_star.
apply flist_crash_xform_sep_star.
eapply flist_crash_xform_sep_star; eauto.
apply flist_crash_xform_sep_star.
(* No more tactics to try *)
Admitted.

