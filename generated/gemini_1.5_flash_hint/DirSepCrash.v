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
Require Import DirSep.
Require Import TreeCrash.
Require Import String.
Require Import DirTree DirTreeDef.
Inductive flatmem_entry_crash : flatmem_entry -> flatmem_entry -> Prop :=
| FMCNothing : flatmem_entry_crash Nothing Nothing
| FMCDir : forall dnum, flatmem_entry_crash (Dir dnum) (Dir dnum)
| FMCFile : forall inum f f',
  DTCrash.file_crash f f' ->
  flatmem_entry_crash (File inum f) (File inum f').
Definition possible_flatmem_crash (m m' : @Mem.mem (list string) (list_eq_dec string_dec) flatmem_entry) :=
  forall a,
  (m a = None /\ m' a = None) \/
  (exists f f', m a = Some f /\ m' a = Some f' /\ flatmem_entry_crash f f').
Definition flatmem_crash_xform p :=
  fun mf => exists mf', p mf' /\ possible_flatmem_crash mf' mf.
Theorem possible_flatmem_crash_mem_union : forall ma mb m', possible_flatmem_crash (mem_union ma mb) m'
  -> @mem_disjoint _ (list_eq_dec string_dec) _ ma mb
  -> exists ma' mb', m' = mem_union ma' mb' /\ mem_disjoint ma' mb' /\
                     possible_flatmem_crash ma ma' /\ possible_flatmem_crash mb mb'.
Proof.
(* original proof tokens: 396 *)
intros.
eexists.
eexists.
split.
(* No more tactics to try *)
Admitted.

Theorem possible_flatmem_crash_disjoint : forall ma mb ma' mb',
  @mem_disjoint _ (list_eq_dec string_dec) _ ma' mb'
  -> possible_flatmem_crash ma ma'
  -> possible_flatmem_crash mb mb'
  -> @mem_disjoint _ (list_eq_dec string_dec) _ ma mb.
(* hint proof tokens: 67 *)
Proof.
  unfold mem_disjoint, possible_flatmem_crash; intros.
  intro Hnot.
  repeat deex.
  destruct (H0 a); destruct (H1 a); try intuition congruence.
  repeat deex.
  apply H.
  do 3 eexists; eauto.
Qed.
Theorem possible_flatmem_crash_union : forall ma mb ma' mb', possible_flatmem_crash ma ma'
  -> possible_flatmem_crash mb mb'
  -> possible_flatmem_crash (mem_union ma mb) (mem_union ma' mb').
(* hint proof tokens: 180 *)
Proof.
  unfold possible_flatmem_crash, mem_union; intros.
  destruct (H a); destruct (H0 a).
  - destruct H1. destruct H2.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    intuition.
  - destruct H1. repeat deex.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 2 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H2 in *.
    right. do 2 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 2 eexists. intuition.
Qed.
Lemma flatmem_crash_xform_sep_star : forall p q,
  flatmem_crash_xform (p * q) <=p=> flatmem_crash_xform p * flatmem_crash_xform q.
Proof.
(* original proof tokens: 122 *)
split.
(* No more tactics to try *)
Admitted.

Theorem flatmem_crash_xform_or_dist : forall p q,
  flatmem_crash_xform (p \/ q) <=p=> flatmem_crash_xform p \/ flatmem_crash_xform q.
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma flatmem_crash_xform_ptsto : forall a f,
  flatmem_crash_xform (a |-> f) =p=> exists f', a |-> f' * [[ flatmem_entry_crash f f' ]].
Proof.
(* original proof tokens: 131 *)
unfold flatmem_crash_xform.
(* No more tactics to try *)
Admitted.

Lemma flatmem_crash_xform_lift_empty : forall P,
  flatmem_crash_xform [[ P ]] <=p=> [[ P ]].
Proof.
(* original proof tokens: 63 *)
split; intros; unfold flatmem_crash_xform; unfold lift_empty; simpl.
split; intros; unfold flatmem_crash_xform; simpl.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_r; eauto.
eapply pimpl_exists_l; [| eapply pimpl_and_l_exists ]; intros; eauto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; [ | eapply pimpl_and_l_exists ]; intros; eauto.
eapply pimpl_exists_r; eauto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_r; eauto.
eapply pimpl_exists_l; [ | eapply pimpl_and_l_exists ]; intros; eauto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; eauto.
apply pimpl_refl.
eapply pimpl_exists_r; eauto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; [|intros]; eauto.
(* Reached max number of model calls *)
Admitted.

Lemma flatmem_crash_xform_emp :
  flatmem_crash_xform emp <=p=> emp.
Proof.
(* original proof tokens: 62 *)
split; auto.
(* No more tactics to try *)
Admitted.

Lemma flatmem_crash_xform_exists : forall T p,
  flatmem_crash_xform (exists (x : T), p x) =p=> exists x, flatmem_crash_xform (p x).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Transparent dir2flatmem2.
Lemma tree_crash_flatmem_crash_xform : forall f f' (P : @pred _ _ _),
  DTCrash.tree_crash f f' ->
  P (dir2flatmem2 f) ->
  (flatmem_crash_xform P) (dir2flatmem2 f').
Proof.
(* original proof tokens: 180 *)

(* No more tactics to try *)
Admitted.

Theorem flatmem_crash_xform_nothing : forall pn,
  flatmem_crash_xform (pn |-> Nothing) =p=> pn |-> Nothing.
(* hint proof tokens: 111 *)
Proof.
  unfold flatmem_crash_xform, ptsto, possible_flatmem_crash, pimpl; intros.
  deex.
  - specialize (H1 pn); intuition; try congruence.
    repeat deex.
    rewrite H in H1. inversion H1; subst.
    inversion H4. congruence.
  - specialize (H1 a'); intuition; try congruence.
    repeat deex.
    rewrite H2 in H3.
    congruence.
    eauto.
Qed.
Theorem flatmem_crash_xform_dir : forall pn dnum,
  flatmem_crash_xform (pn |-> Dir dnum) =p=> pn |-> Dir dnum.
(* hint proof tokens: 111 *)
Proof.
  unfold flatmem_crash_xform, ptsto, possible_flatmem_crash, pimpl; intros.
  deex.
  - specialize (H1 pn); intuition; try congruence.
    repeat deex.
    rewrite H in H1. inversion H1; subst.
    inversion H4. congruence.
  - specialize (H1 a'); intuition; try congruence.
    repeat deex.
    rewrite H2 in H3.
    congruence.
    eauto.
Qed.
Theorem flatmem_crash_xform_file : forall pn inum f,
  flatmem_crash_xform (pn |-> File inum f) =p=>
    exists f', pn |-> File inum f' * [[ DTCrash.file_crash f f' ]].
(* hint proof tokens: 125 *)
Proof.
  unfold flatmem_crash_xform, ptsto, possible_flatmem_crash, pimpl; intros.
  deex.
  specialize (H1 pn) as H1'; intuition; try congruence.
  repeat deex.
  rewrite H in H3. inversion H3; subst.
  inversion H5. subst.
  eexists.
  eapply sep_star_lift_apply'; eauto.
  intuition.
  specialize (H1 a').
  intuition.
  repeat deex.
  rewrite H2 in H6; try congruence; eauto.
Qed.
Instance flatmem_crash_xform_pimpl_proper :
  Proper (pimpl ==> pimpl) flatmem_crash_xform.
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
