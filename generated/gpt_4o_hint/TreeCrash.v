Require Import DirName.
Require Import Balloc.
Require Import Prog.
Require Import BasicProg.
Require Import Bool.
Require Import Word.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import FSLayout.
Require Import Pred PredCrash.
Require Import Arith.
Require Import GenSepN.
Require Import List ListUtils.
Require Import Hoare.
Require Import Log.
Require Import SepAuto.
Require Import Array.
Require Import FunctionalExtensionality.
Require Import AsyncDisk.
Require Import DiskSet.
Require Import SyncedMem.
Require Import GenSepAuto.
Require Import BFileCrash.
Require Import Lia.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeNames.
Require Import DirTreeInodes.
Import ListNotations.
Module SDIR := DirCache.CacheOneDir.
Set Implicit Arguments.
Module DTCrash.
Definition file_crash (f f' : dirfile) : Prop :=
    exists c c',
    BFILE.file_crash (BFILE.mk_bfile (DFData f) (DFAttr f) c)
                     (BFILE.mk_bfile (DFData f') (DFAttr f') c').
Inductive tree_crash : dirtree -> dirtree -> Prop :=
    | TCFile : forall inum f f',
               file_crash f f' ->
               tree_crash (TreeFile inum f) (TreeFile inum f')
    | TCDir  : forall inum st st',
               map fst st = map fst st' ->
               Forall2 tree_crash (map snd st) (map snd st') ->
               tree_crash (TreeDir inum st) (TreeDir inum st').
Theorem tree_crash_trans : forall t1 t2 t3,
    tree_crash t1 t2 ->
    tree_crash t2 t3 ->
    tree_crash t1 t3.
(* hint proof tokens: 221 *)
Proof.
    induction t1 using dirtree_ind2; simpl; intros.
    inversion H; subst. inversion H0; subst. econstructor.
      unfold file_crash in *. repeat deex. do 2 eexists. eapply file_crash_trans; eauto.
    inversion H0; subst. inversion H1; subst. constructor. congruence.
    generalize dependent st'. generalize dependent st'0.
    induction tree_ents; simpl; intros.
    - destruct st'; simpl in *; try congruence.
    - destruct st'; destruct st'0; simpl in *; try congruence.
      inversion H6. inversion H8. inversion H. inversion H4. inversion H5. subst; simpl in *.
      constructor; eauto.
      eapply IHtree_ents. eauto.
      all: try match goal with | [ |- Forall2 _ _ _ ] => eauto end.
      all: eauto.
      constructor; eauto.
      constructor; eauto.
  Qed.
Lemma flist_crash_xform_dirlist_pred : forall tree_ents p,
    Forall
      (fun t => flist_crash_xform (p t) =p=> exists t', [[ tree_crash t t' ]] * p t')
      (map snd tree_ents) ->
    flist_crash_xform (dirlist_pred p tree_ents) =p=>
      exists tree_ents',
      [[ Forall2 tree_crash (map snd tree_ents) (map snd tree_ents') ]] *
      [[ map fst tree_ents = map fst tree_ents' ]] *
      dirlist_pred p tree_ents'.
Proof.
(* skipped proof tokens: 117 *)
Admitted.
Lemma tree_dir_names_pred'_unchanged : forall tree_ents tree_ents',
    map fst tree_ents = map fst tree_ents' ->
    map (fun e => dirtree_inum e) (map snd tree_ents) = map (fun e => dirtree_inum e) (map snd tree_ents') ->
    map (fun e => dirtree_isdir e) (map snd tree_ents) = map (fun e => dirtree_isdir e) (map snd tree_ents') ->
    tree_dir_names_pred' tree_ents =p=> tree_dir_names_pred' tree_ents'.
(* hint proof tokens: 78 *)
Proof.
    induction tree_ents; intros; destruct tree_ents'; simpl in *; try congruence.
    destruct a; destruct p; simpl in *.
    inversion H; clear H.
    inversion H0; clear H0.
    inversion H1; clear H1.
    subst.
    rewrite IHtree_ents; eauto.
  Qed.
Lemma flist_crash_xform_tree_dir_names_pred : forall tree_ents tree_ents' xp inum,
    map fst tree_ents = map fst tree_ents' ->
    map (fun e => dirtree_inum e) (map snd tree_ents) = map (fun e => dirtree_inum e) (map snd tree_ents') ->
    map (fun e => dirtree_isdir e) (map snd tree_ents) = map (fun e => dirtree_isdir e) (map snd tree_ents') ->
    flist_crash_xform (tree_dir_names_pred xp inum tree_ents) =p=>
      tree_dir_names_pred xp inum tree_ents'.
(* hint proof tokens: 120 *)
Proof.
    unfold tree_dir_names_pred; intros.
    rewrite flist_crash_xform_exists. norml; unfold stars; simpl.
    rewrite flist_crash_xform_exists. norml; unfold stars; simpl.
    repeat rewrite flist_crash_xform_sep_star.
    repeat rewrite flist_crash_xform_lift_empty.
    rewrite flist_crash_xform_ptsto.
    cancel.
    eapply SDIR.crash_rep; eauto.
    pred_apply.
    apply tree_dir_names_pred'_unchanged; eauto.
  Qed.
Lemma tree_crash_preserves_dirtree_inum : forall t t',
    tree_crash t t' ->
    dirtree_inum t = dirtree_inum t'.
(* hint proof tokens: 14 *)
Proof.
    inversion 1; auto.
  Qed.
Lemma tree_crash_preserves_dirtree_isdir : forall t t',
    tree_crash t t' ->
    dirtree_isdir t = dirtree_isdir t'.
(* hint proof tokens: 14 *)
Proof.
    inversion 1; auto.
  Qed.
Lemma flist_crash_xform_tree_pred : forall xp t,
    flist_crash_xform (tree_pred xp t) =p=> exists t', [[ tree_crash t t' ]] * tree_pred xp t'.
(* hint proof tokens: 244 *)
Proof.
    induction t using dirtree_ind2; simpl; intros.
    - rewrite flist_crash_xform_exists.
      setoid_rewrite flist_crash_xform_sep_star.
      setoid_rewrite flist_crash_xform_ptsto.
      setoid_rewrite flist_crash_xform_lift_empty.
      norml. destruct f'. cancel.
      instantiate (t' := TreeFile inum (mk_dirfile _ _)). cbn. cancel.
      econstructor; eauto.
      unfold file_crash. do 2 eexists. eauto.
    - rewrite flist_crash_xform_sep_star.
      rewrite flist_crash_xform_dirlist_pred by eauto.
      cancel.
      eassign (TreeDir inum tree_ents').
      cancel.
      apply flist_crash_xform_tree_dir_names_pred; eauto.
      eapply Forall2_to_map_eq. apply tree_crash_preserves_dirtree_inum. eauto.
      eapply Forall2_to_map_eq. apply tree_crash_preserves_dirtree_isdir. eauto.
      constructor; eauto.
  Qed.
Lemma flist_crash_xform_freelist : forall (FP : BFILE.bfile -> Prop) xp frees freepred ms,
    (forall f f', BFILE.file_crash f f' -> FP f -> FP f') ->
    IAlloc.Alloc.rep FP xp frees freepred ms =p=>
      IAlloc.Alloc.rep FP xp frees freepred ms *
      [[ flist_crash_xform freepred =p=> freepred ]].
Proof.
(* skipped proof tokens: 170 *)
Admitted.
Lemma xform_tree_rep : forall xp F t ilist frees ms msll' sm,
     crash_xform (rep xp F t ilist frees ms sm) =p=>
     exists t',
      [[ tree_crash t t' ]] * 
      rep xp (flist_crash_xform F) t' ilist frees (BFILE.ms_empty msll') sm_synced.
Proof.
(* skipped proof tokens: 219 *)
Admitted.
Theorem tree_crash_find_name :
    forall fnlist t t' subtree,
    tree_crash t t' ->
    find_subtree fnlist t = Some subtree ->
    exists subtree',
    find_subtree fnlist t' = Some subtree' /\
    tree_crash subtree subtree'.
Proof.
(* skipped proof tokens: 290 *)
Admitted.
Theorem tree_crash_find_none :
    forall fnlist t t',
    tree_crash t t' ->
    find_subtree fnlist t = None ->
    find_subtree fnlist t' = None.
Proof.
(* skipped proof tokens: 265 *)
Admitted.
Lemma tree_crash_find_subtree_root: forall t t' inum,
    tree_crash t t' ->
    (exists elem, find_subtree [] t = Some (TreeDir inum elem)) ->
    (exists elem', find_subtree [] t' = Some (TreeDir inum elem')).
(* hint proof tokens: 92 *)
Proof.
    intros.
    destruct t.
    - destruct H0.
      inversion H0.
    - destruct H0.
      unfold find_subtree in *. simpl in *.
      destruct t'.
      inversion H0.
      inversion H0.
      subst; simpl.
      exfalso.
      inversion H.
      inversion H0.
      subst; simpl.
      inversion H.
      subst; simpl; eauto.
  Qed.
Lemma tree_crash_find_name_root: forall t t' inum,
    tree_crash t t' ->
    find_name [] t = Some (inum, true) ->
    find_name [] t' = Some (inum, true).
Proof.
(* skipped proof tokens: 112 *)
Admitted.
Theorem file_crash_exists : forall file, exists file',
    BFILE.file_crash file file'.
(* hint proof tokens: 67 *)
Proof.
    unfold BFILE.file_crash; intros.
    eexists.
    exists (map fst (BFILE.BFData file)).
    intuition.
    split; intros.
    rewrite map_length; eauto.
    unfold vsmerge. constructor.
    erewrite selN_map; eauto.
  Qed.
Theorem tree_crash_exists : forall tree, exists tree',
    tree_crash tree tree'.
(* hint proof tokens: 155 *)
Proof.
    induction tree using dirtree_ind2; intros.
    edestruct file_crash_exists as [ [] H].
    eexists (TreeFile _ (mk_dirfile _ _)).
    econstructor; cbn. unfold file_crash. do 2 eexists. eauto.
    induction tree_ents.
    eexists; constructor; eauto. constructor.
    destruct a; simpl in *.
    inversion H.
    edestruct IHtree_ents; eauto.
    inversion H4.
    repeat deex.
    exists (TreeDir inum ((s, tree') :: st')).
    constructor. simpl; f_equal; auto.
    constructor; auto.
  Unshelve.
    exact None.
  Qed.
Theorem tree_crash_update_subtree' :
    forall pn tree subtree tree' subtree',
    tree_crash tree tree' ->
    tree_crash subtree subtree' ->
    tree_crash (update_subtree pn subtree tree) (update_subtree pn subtree' tree').
Proof.
(* skipped proof tokens: 256 *)
Admitted.
Theorem tree_crash_tree_names_distinct : forall t t',
    tree_crash t t' ->
    tree_names_distinct t ->
    tree_names_distinct t'.
Proof.
(* skipped proof tokens: 171 *)
Admitted.
Theorem tree_crash_tree_inodes_permutation : forall t t',
    tree_crash t t' ->
    permutation addr_eq_dec (tree_inodes t) (tree_inodes t').
Proof.
(* skipped proof tokens: 215 *)
Admitted.
Theorem tree_crash_tree_inodes_distinct : forall t t',
    tree_crash t t' ->
    tree_inodes_distinct t ->
    tree_inodes_distinct t'.
(* hint proof tokens: 57 *)
Proof.
    unfold tree_inodes_distinct; intros.
    eapply NoDup_incl_count; eauto.
    eapply permutation_incl_count.
    apply permutation_comm.
    eapply tree_crash_tree_inodes_permutation; eauto.
  Qed.
Theorem tree_crash_update_subtree :
    forall pn tree subtree updated_tree_crashed,
    tree_names_distinct tree ->
    tree_crash (update_subtree pn subtree tree) updated_tree_crashed ->
    exists tree_crashed subtree_crashed,
    tree_crash tree tree_crashed /\
    tree_crash subtree subtree_crashed /\
    updated_tree_crashed = update_subtree pn subtree_crashed tree_crashed.
Proof.
(* original proof tokens: 474 *)

(* No more tactics to try *)
Admitted.

Lemma file_crash_data_length : forall f f',
    file_crash f f' -> length (DFData f) = length (DFData f').
(* hint proof tokens: 41 *)
Proof.
    unfold file_crash; intros.
    repeat deex.
    eapply BFILE.file_crash_data_length in H; simpl in *.
    eauto.
  Qed.
Lemma file_crash_synced : forall f f',
    file_crash (synced_dirfile f) f' ->
    f' = synced_dirfile f.
(* hint proof tokens: 101 *)
Proof.
    unfold file_crash, synced_dirfile; intros.
    repeat deex.
    edestruct BFILE.file_crash_synced; eauto.
    pose proof (BFILE.fsynced_synced_file (BFILE.mk_bfile (DFData f) (DFAttr f) c)).
    unfold BFILE.synced_file in H0; simpl in *.
    eauto.

    destruct f'; simpl in *.
    subst; eauto.
  Qed.
Lemma dirfile_crash_exists : forall f, exists f',
    file_crash f f'.
Proof.
(* skipped proof tokens: 69 *)
Admitted.
End DTCrash.
