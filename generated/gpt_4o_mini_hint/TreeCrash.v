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
Proof.
(* original proof tokens: 221 *)

(* No more tactics to try *)
Admitted.

Lemma flist_crash_xform_dirlist_pred : forall tree_ents p,
    Forall
      (fun t => flist_crash_xform (p t) =p=> exists t', [[ tree_crash t t' ]] * p t')
      (map snd tree_ents) ->
    flist_crash_xform (dirlist_pred p tree_ents) =p=>
      exists tree_ents',
      [[ Forall2 tree_crash (map snd tree_ents) (map snd tree_ents') ]] *
      [[ map fst tree_ents = map fst tree_ents' ]] *
      dirlist_pred p tree_ents'.
(* hint proof tokens: 117 *)
Proof.
    induction tree_ents; simpl; intros.
    - rewrite flist_crash_xform_emp. cancel.
      eassign (@nil (string * dirtree)); cancel.
      constructor.
      constructor.
    - destruct a. rewrite flist_crash_xform_sep_star.
      inversion H; subst.
      rewrite H2.
      rewrite IHtree_ents by eauto.
      cancel.
      eassign ((s, t') :: tree_ents').
      cancel.
      constructor; eauto.
      simpl; congruence.
  Qed.
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
Proof.
(* original proof tokens: 120 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 14 *)
(* generated proof tokens: 15 *)

intros.
inversion H; auto.
Qed.

Lemma flist_crash_xform_tree_pred : forall xp t,
    flist_crash_xform (tree_pred xp t) =p=> exists t', [[ tree_crash t t' ]] * tree_pred xp t'.
Proof.
(* original proof tokens: 244 *)

(* No more tactics to try *)
Admitted.

Lemma flist_crash_xform_freelist : forall (FP : BFILE.bfile -> Prop) xp frees freepred ms,
    (forall f f', BFILE.file_crash f f' -> FP f -> FP f') ->
    IAlloc.Alloc.rep FP xp frees freepred ms =p=>
      IAlloc.Alloc.rep FP xp frees freepred ms *
      [[ flist_crash_xform freepred =p=> freepred ]].
(* hint proof tokens: 170 *)
Proof.
    unfold IAlloc.Alloc.rep, IAlloc.Alloc.Alloc.rep; intros.
    cancel.
    match goal with H: _ <=p=> _ |- _ => rewrite H end.
    repeat match goal with
      Hb: context [BFILE.file_crash],
      Hother: _ |- _ => clear Hother
    end.
    induction frees; simpl.
    rewrite flist_crash_xform_emp; auto.
    rewrite flist_crash_xform_sep_star. rewrite flist_crash_xform_exists.
    rewrite IHfrees.
    norml; unfold stars; simpl.
    rewrite flist_crash_xform_sep_star.
    rewrite flist_crash_xform_lift_empty.
    rewrite flist_crash_xform_ptsto. cancel. eauto.
  Qed.
Lemma xform_tree_rep : forall xp F t ilist frees ms msll' sm,
     crash_xform (rep xp F t ilist frees ms sm) =p=>
     exists t',
      [[ tree_crash t t' ]] * 
      rep xp (flist_crash_xform F) t' ilist frees (BFILE.ms_empty msll') sm_synced.
(* hint proof tokens: 219 *)
Proof.
    unfold rep; intros.
    xform_norm.
    rewrite BFILE.xform_rep.
    rewrite IAlloc.xform_rep.
    rewrite flist_crash_xform_freelist.
    norml; unfold stars; simpl.
    eapply flist_crash_flist_crash_xform in H0; eauto.
    apply flist_crash_xform_sep_star in H0. rewrite flist_crash_xform_sep_star in H0.
    rewrite flist_crash_xform_tree_pred in H0.
    destruct_lift H0.
    unfold IAlloc.rep; cancel.
    rewrite <- BFILE.rep_clear_freelist.
    rewrite <- BFILE.rep_clear_icache.
    rewrite <- IAlloc.rep_clear_cache.
    cancel.
    eauto.
    pred_apply.
    cancel; auto.
    intros; eapply BFILE.freepred_file_crash; eauto.
  Unshelve.
    all: exact (LOG.mk_memstate0 (Cache.BUFCACHE.cache0 1)).
  Qed.
Theorem tree_crash_find_name :
    forall fnlist t t' subtree,
    tree_crash t t' ->
    find_subtree fnlist t = Some subtree ->
    exists subtree',
    find_subtree fnlist t' = Some subtree' /\
    tree_crash subtree subtree'.
(* hint proof tokens: 290 *)
Proof.
    induction fnlist.
    - simpl; intros.
      eexists; intuition eauto.
      inversion H0; subst; auto.
    - intros.
      inversion H0.
      destruct t; try congruence.
      inversion H; subst.
      generalize dependent st'.
      induction l; intros.
      + simpl in *. congruence.
      + destruct st'; try solve [ simpl in *; congruence ].
        destruct p.
        unfold find_subtree_helper in H2 at 1.
        destruct a0.
        simpl in H2.
        destruct (string_dec s0 a).
        * subst.
          edestruct IHfnlist.
          2: apply H2.
          inversion H6; eauto.
          eexists.
          intuition eauto.
          inversion H4; subst.
          simpl; destruct (string_dec s s); try congruence.
        * edestruct IHl.

          eauto.
          eauto.
          all: try solve [ inversion H4; exact H5 ].
          all: try solve [ inversion H6; eauto ].

          constructor. inversion H4; eauto.
          inversion H. inversion H8; eauto.

          exists x. intuition.
          simpl.
          inversion H4; subst. destruct (string_dec s a); try congruence.
          apply H3.
  Qed.
Theorem tree_crash_find_none :
    forall fnlist t t',
    tree_crash t t' ->
    find_subtree fnlist t = None ->
    find_subtree fnlist t' = None.
Proof.
(* original proof tokens: 265 *)

(* No more tactics to try *)
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
(* original proof tokens: 112 *)

(* No more tactics to try *)
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
Proof.
(* original proof tokens: 155 *)
induction tree; eauto using file_crash_exists.
(* No more tactics to try *)
Admitted.

Theorem tree_crash_update_subtree' :
    forall pn tree subtree tree' subtree',
    tree_crash tree tree' ->
    tree_crash subtree subtree' ->
    tree_crash (update_subtree pn subtree tree) (update_subtree pn subtree' tree').
Proof.
(* original proof tokens: 256 *)

(* No more tactics to try *)
Admitted.

Theorem tree_crash_tree_names_distinct : forall t t',
    tree_crash t t' ->
    tree_names_distinct t ->
    tree_names_distinct t'.
(* hint proof tokens: 171 *)
Proof.
    induction t using dirtree_ind2; simpl in *; intros.
    inversion H; constructor.
    inversion H0; subst.
    inversion H1; subst.
    constructor; try congruence.
    eapply forall_forall2_l in H; try ( eapply forall2_length; eauto ).
    eapply forall_forall2_l in H5; try ( eapply forall2_length; eauto ).
    eapply forall2_forall_r; try ( eapply forall2_length; eauto ).
    eapply forall2_impl. apply H.
    eapply forall2_impl. apply H5.
    eapply forall2_impl. apply H6.
    apply forall2_lift; try ( eapply forall2_length; eauto ).
    intros; eauto.
  Qed.
Theorem tree_crash_tree_inodes_permutation : forall t t',
    tree_crash t t' ->
    permutation addr_eq_dec (tree_inodes t) (tree_inodes t').
(* hint proof tokens: 215 *)
Proof.
    induction t using dirtree_ind2; simpl; intros.
    - inversion H; subst. constructor.
    - inversion H0; subst.
      generalize dependent st'.
      induction tree_ents; intros; destruct st'; simpl in *; try congruence.
      destruct a. destruct p.
      inversion H5; subst.
      inversion H; subst.
      repeat rewrite cons_app with (l := app _ _).
      eapply permutation_trans. apply permutation_app_comm. rewrite <- app_assoc.
      eapply permutation_trans. 2: apply permutation_app_comm. rewrite <- app_assoc.
      eapply permutation_app_split. eauto.
      eapply permutation_trans. apply permutation_app_comm.
      eapply permutation_trans. 2: apply permutation_app_comm.
      eapply IHtree_ents; eauto.
      constructor; eauto.
      inversion H0; subst. inversion H10; subst. eauto.
      inversion H0; subst. inversion H10; subst. eauto.
  Qed.
Theorem tree_crash_tree_inodes_distinct : forall t t',
    tree_crash t t' ->
    tree_inodes_distinct t ->
    tree_inodes_distinct t'.
Proof.
(* original proof tokens: 57 *)

(* No more tactics to try *)
Admitted.

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
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

End DTCrash.
