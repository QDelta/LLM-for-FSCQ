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
(* hint proof tokens: 396 *)
Proof.
  intros.
  exists (fun a => match ma a with | None => None | Some v => m' a end).
  exists (fun a => match mb a with | None => None | Some v => m' a end).
  repeat split.

  - unfold mem_union; apply functional_extensionality; intros.
    case_eq (ma x); case_eq (mb x); case_eq (m' x); auto.
    intros; unfold possible_flatmem_crash in *.
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
  - unfold possible_flatmem_crash in *; intro a.
    case_eq (ma a); intros; [right|left]; auto.
    pose proof (mem_union_addr a H0 H1).
    destruct (H a); destruct H3; try congruence.
    repeat deex. do 2 eexists. intuition eauto.
    congruence.
  - unfold possible_flatmem_crash in *; intro a.
    case_eq (mb a); intros; [right|left]; auto.
    rewrite mem_disjoint_comm in H0.
    pose proof (mem_union_addr a H0 H1); rewrite mem_union_comm in H2 by auto.
    destruct (H a); destruct H3; try congruence.
    repeat deex. do 2 eexists. intuition eauto.
    congruence.
Qed.
Theorem possible_flatmem_crash_disjoint : forall ma mb ma' mb',
  @mem_disjoint _ (list_eq_dec string_dec) _ ma' mb'
  -> possible_flatmem_crash ma ma'
  -> possible_flatmem_crash mb mb'
  -> @mem_disjoint _ (list_eq_dec string_dec) _ ma mb.
Proof.
(* skipped proof tokens: 67 *)
Admitted.
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
(* hint proof tokens: 122 *)
Proof.
  unfold_sep_star.
  unfold flatmem_crash_xform, piff, pimpl.
  split; intros; repeat deex.
  - edestruct possible_flatmem_crash_mem_union; eauto.
    repeat deex.
    do 2 eexists. intuition eauto.
  - eexists. split.
    do 2 eexists. intuition idtac. 2: eauto. 2: eauto.
    eapply possible_flatmem_crash_disjoint; eauto.
    eapply possible_flatmem_crash_union; eauto.
Qed.
Theorem flatmem_crash_xform_or_dist : forall p q,
  flatmem_crash_xform (p \/ q) <=p=> flatmem_crash_xform p \/ flatmem_crash_xform q.
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma flatmem_crash_xform_ptsto : forall a f,
  flatmem_crash_xform (a |-> f) =p=> exists f', a |-> f' * [[ flatmem_entry_crash f f' ]].
(* hint proof tokens: 131 *)
Proof.
  unfold flatmem_crash_xform, ptsto, pimpl, possible_flatmem_crash, and, lift; intros.
  repeat deex.
  specialize (H1 a) as H1a; intuition; try congruence; repeat deex.
  exists f'.
  eapply sep_star_lift_apply'.
  2: congruence.
  intuition (try congruence).
  specialize (H1 a') as H1a'; intuition; try congruence.
  repeat deex; try congruence. rewrite H2 in * by eauto. congruence.
Qed.
Lemma flatmem_crash_xform_lift_empty : forall P,
  flatmem_crash_xform [[ P ]] <=p=> [[ P ]].
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Lemma flatmem_crash_xform_emp :
  flatmem_crash_xform emp <=p=> emp.
Proof.
(* skipped proof tokens: 62 *)
Admitted.
Lemma flatmem_crash_xform_exists : forall T p,
  flatmem_crash_xform (exists (x : T), p x) =p=> exists x, flatmem_crash_xform (p x).
Proof.
(* skipped proof tokens: 9 *)
Admitted.
Transparent dir2flatmem2.
Lemma tree_crash_flatmem_crash_xform : forall f f' (P : @pred _ _ _),
  DTCrash.tree_crash f f' ->
  P (dir2flatmem2 f) ->
  (flatmem_crash_xform P) (dir2flatmem2 f').
Proof.
(* skipped proof tokens: 180 *)
Admitted.
Theorem flatmem_crash_xform_nothing : forall pn,
  flatmem_crash_xform (pn |-> Nothing) =p=> pn |-> Nothing.
Proof.
(* skipped proof tokens: 111 *)
Admitted.
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
Proof.
(* original proof tokens: 125 *)

(* No more tactics to try *)
Admitted.

Instance flatmem_crash_xform_pimpl_proper :
  Proper (pimpl ==> pimpl) flatmem_crash_xform.
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
