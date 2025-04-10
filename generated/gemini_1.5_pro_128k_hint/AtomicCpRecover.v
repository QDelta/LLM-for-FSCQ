Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Lia.
Require Import Hashmap.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirName.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List ListUtils.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import GroupLog.
Require Import SuperBlock.
Require Import DiskSet.
Require Import AsyncFS.
Require Import String.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreeNames.
Require Import DirTreeSafe.
Require Import TreeCrash.
Require Import TreeSeq.
Require Import DirSep.
Require Import DirSepCrash.
Require Import SyncedMem.
Require Import AtomicCp.
Require Import BFileCrash.
Import TREESEQ.
Import DTCrash.
Import ListNotations.
Import ATOMICCP.
Set Implicit Arguments.
Lemma file_crash_trans: forall f1 f2 f3,
  file_crash f1 f2 ->
  file_crash f2 f3 ->
  file_crash f1 f3.
(* hint proof tokens: 36 *)
Proof.
  unfold file_crash; intros.
  repeat deex.
  do 2 eexists.
  eapply file_crash_trans; eauto.
Qed.
Lemma possible_fmem_crash_trans: forall m1 m2 m3,
  possible_fmem_crash m1 m2 ->
  possible_fmem_crash m2 m3 ->
  possible_fmem_crash m1 m3.
(* hint proof tokens: 95 *)
Proof.
  unfold possible_fmem_crash; intros.
  specialize (H a).
  specialize (H0 a).
  intuition;
  try solve [repeat deex; congruence].
  repeat deex.
  rewrite H0 in H1; inversion H1; subst; clear H1.
  right; do 2 eexists; repeat split; eauto.
  eapply BFileCrash.file_crash_trans; eauto.
Qed.
Lemma flist_crash_xform_idem: forall F,
  flist_crash_xform (flist_crash_xform F) =p=> flist_crash_xform F.
(* hint proof tokens: 52 *)
Proof.
  unfold flist_crash_xform; unfold pimpl; simpl; intros.
  repeat deex; intuition.
  exists mf'0; split; auto.
  eapply possible_fmem_crash_trans; eauto.
Qed.
Lemma treeseq_in_ds_crash_idem: forall ds ts Fm Ftop fsxp sm mscs ,
  treeseq_in_ds (crash_xform (crash_xform Fm))
      (flist_crash_xform (flist_crash_xform Ftop)) fsxp sm mscs ts ds
  -> treeseq_in_ds (crash_xform Fm) (flist_crash_xform Ftop) fsxp sm mscs ts ds.
Proof.
(* skipped proof tokens: 480 *)
Admitted.
Lemma flatmem_entry_crash_trans: forall f1 f2 f3,
  flatmem_entry_crash f1 f2 ->  
  flatmem_entry_crash f2 f3 ->
  flatmem_entry_crash f1 f3.
Proof.
(* skipped proof tokens: 57 *)
Admitted.
Lemma possible_flatmem_crash_trans: forall m1 m2 m3,
  possible_flatmem_crash m1 m2 ->
  possible_flatmem_crash m2 m3 ->
  possible_flatmem_crash m1 m3.
Proof.
(* original proof tokens: 94 *)
(* generated proof tokens: 97 *)

Proof.
  unfold possible_flatmem_crash; intros.
  specialize (H a).
  specialize (H0 a).
  intuition;
  try solve [repeat deex; congruence].
  repeat deex.
  rewrite H0 in H1; inversion H1; subst; clear H1.
  right; do 2 eexists; repeat split; eauto.
  eapply flatmem_entry_crash_trans; eauto.
Qed.

Lemma flatmem_crash_xform_idem: forall F,
  flatmem_crash_xform (flatmem_crash_xform F) =p=> flatmem_crash_xform F.
Proof.
(* skipped proof tokens: 47 *)
Admitted.
Lemma treeseq_pred_tree_rep_recover_idem: forall ts Ftree srcpath temp_fn srcinum file
  dstbase dstname dstfile,
  treeseq_pred (tree_rep_recover ( flatmem_crash_xform (flatmem_crash_xform Ftree)) srcpath [temp_fn] srcinum file dstbase dstname dstfile) ts ->
  treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dstfile) ts.
(* hint proof tokens: 458 *)
Proof.
  intros; destruct ts, l; simpl in *.
  
  -
  unfold treeseq_pred, NEforall, tree_rep_recover in *; simpl in *.
  intuition.
  unfold tree_with_src in *.
  destruct_lift H2.
  rewrite flatmem_crash_xform_idem in H2.
  left; pred_apply; cancel.
  apply Forall_nil.
  unfold tree_with_dst in *.
  destruct_lift H2.
  rewrite flatmem_crash_xform_idem in H2.
  right; pred_apply; cancel.
  apply Forall_nil.
  
  -
   unfold treeseq_pred, tree_rep_recover in *; simpl in *.
   inversion H; subst; simpl in *; clear H.
   intuition.
   split; simpl.
   repeat (split; auto).
   unfold tree_with_src in *.
   destruct_lift H2.
   rewrite flatmem_crash_xform_idem in H2.
   left; pred_apply; cancel.
   induction H1.
   apply Forall_nil.
   apply Forall_cons; auto.
   intuition.
   unfold tree_with_src in *.
   destruct_lift H5.
   rewrite flatmem_crash_xform_idem in H5.
   left; pred_apply; cancel.
   unfold tree_with_dst in *.
   destruct_lift H5.
   rewrite flatmem_crash_xform_idem in H5.
   right; pred_apply; cancel.
   
   split; simpl.
   repeat (split; auto).
   unfold tree_with_dst in *.
   destruct_lift H2.
   rewrite flatmem_crash_xform_idem in H2.
   right; pred_apply; cancel.
   induction H1.
   apply Forall_nil.
   apply Forall_cons; auto.
   intuition.
   unfold tree_with_src in *.
   destruct_lift H5.
   rewrite flatmem_crash_xform_idem in H5.
   left; pred_apply; cancel.
   unfold tree_with_dst in *.
   destruct_lift H5.
   rewrite flatmem_crash_xform_idem in H5.
   right; pred_apply; cancel.
Qed.
Lemma treeseq_pred_tree_rep_idem: forall ts Ftree srcpath temp_fn srcinum file
  dstbase dstname dstfile dinum,
  treeseq_pred (tree_rep (flatmem_crash_xform (flatmem_crash_xform Ftree)) srcpath [temp_fn] srcinum file dinum dstbase dstname dstfile) ts ->
  treeseq_pred (tree_rep (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dinum dstbase dstname dstfile) ts.
(* hint proof tokens: 793 *)
Proof.
  intros; destruct ts, l; simpl in *.
  
  -
  unfold treeseq_pred, NEforall, tree_rep in *; simpl in *.
  intuition.
  unfold tree_with_tmp in *.
  deex.
  destruct_lift H2.
  rewrite flatmem_crash_xform_idem in H2.
  left; pred_apply; cancel.
  apply Forall_nil.
  unfold tree_with_src in *.
  destruct_lift H3.
  rewrite flatmem_crash_xform_idem in H2.
  right; left; pred_apply; cancel.
  apply Forall_nil.
  unfold tree_with_dst in *.
  destruct_lift H3.
  rewrite flatmem_crash_xform_idem in H2.
  right; right; pred_apply; cancel.
  apply Forall_nil.
  
  -
   unfold treeseq_pred, tree_rep in *; simpl in *.
   inversion H; subst; simpl in *; clear H.
   intuition.
   split; simpl.
   repeat (split; auto).
   unfold tree_with_tmp in *.
   deex; destruct_lift H2.
   rewrite flatmem_crash_xform_idem in H2.
   left; pred_apply; cancel.
   induction H1.
   apply Forall_nil.
   apply Forall_cons; auto.
   intuition.
   unfold tree_with_tmp in *.
  deex.
  destruct_lift H5.
  rewrite flatmem_crash_xform_idem in H5.
  left; pred_apply; cancel.
  unfold tree_with_src in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; left; pred_apply; cancel.
  unfold tree_with_dst in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; right; pred_apply; cancel.
   
   split; simpl.
   repeat (split; auto).
   unfold tree_with_src in *.
   destruct_lift H3.
   rewrite flatmem_crash_xform_idem in H2.
   right; left; pred_apply; cancel.
   induction H1.
   apply Forall_nil.
   apply Forall_cons; auto.
   intuition.
   unfold tree_with_tmp in *.
  deex.
  destruct_lift H5.
  rewrite flatmem_crash_xform_idem in H5.
  left; pred_apply; cancel.
  unfold tree_with_src in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; left; pred_apply; cancel.
  unfold tree_with_dst in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; right; pred_apply; cancel.
   
   split; simpl.
   repeat (split; auto).
   unfold tree_with_dst in *.
   destruct_lift H3.
   rewrite flatmem_crash_xform_idem in H2.
   right; right; pred_apply; cancel.
   induction H1.
   apply Forall_nil.
   apply Forall_cons; auto.
   intuition.
   unfold tree_with_tmp in *.
  deex.
  destruct_lift H5.
  rewrite flatmem_crash_xform_idem in H5.
  left; pred_apply; cancel.
  unfold tree_with_src in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; left; pred_apply; cancel.
  unfold tree_with_dst in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; right; pred_apply; cancel.
Qed.
Theorem pimpl_or2:
  forall T pre pre' pre'' (pr: prog T),
  {{pre}} pr ->
  {{pre'}} pr ->
  (forall vm hm done crash, (pre'' vm hm done crash =p=> pre vm hm done crash \/ pre' vm hm done crash)) ->
  {{ pre''}} pr.
(* hint proof tokens: 60 *)
Proof.
  unfold corr2; intros.
  specialize (H1 vm hm done crash).
  apply H1 in H2.
  apply pimpl_or_apply in H2.
  intuition.
  eapply H; eauto.
  eapply H0; eauto.
Qed.
Theorem atomic_cp_recover_ok :
    {< Fm Ftop Ftree fsxp cs mscs ds sm t ts' srcpath file srcinum tinum dstfile (dstbase: list string) (dstname:string) dfile tinum',
    PRE:hm
      LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
      ([[ treeseq_in_ds Fm Ftop fsxp sm mscs ts' ds ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts']]
       \/
       ([[ treeseq_in_ds Fm Ftop fsxp sm mscs (pushd t ts') ds ]] *
       [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum' dstbase dstname dfile t ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]]))
    POST:hm' RET:r
      [[ isError r ]] * any \/
      exists d sm' t mscs',
      [[ r = OK (mscs', fsxp) ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') sm' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' (t, nil) (d, nil) ]] *
      ([[ treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dstfile) (t, nil) ]] \/
       [[ treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dfile) (t, nil) ]])
    XCRASH:hm'
      (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts' ds ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]])
       \/
     (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs (pushd t ts') ds ]] *
      [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum' dstbase dstname dfile t ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]])
       \/
      exists ts' ds' sm' mscs' dstfile' tinum',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' ts' ds' ]] *
      [[ treeseq_pred (tree_rep (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file tinum' dstbase dstname dstfile') ts' ]] *
      ([[ file_crash dstfile dstfile' ]] \/ [[ file_crash dfile dstfile' ]])
    >} atomic_cp_recover.
Proof.
(* skipped proof tokens: 324 *)
Admitted.
Theorem atomic_cp_with_recover_ok : forall fsxp srcinum mscs dstbase dstname ,
    {X<< Fm Ftop Ftree ds sm ts srcpath file v0 dstfile tinum,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_src Ftree srcpath [temp_fn] srcinum file dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[ dirtree_inum (TStree ts!!) = the_dnum ]]
    POST:hm' RET:^(mscs', r)
      exists ds' sm' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       (([[r = false ]] *
        ([[ treeseq_in_ds Fm Ftop fsxp sm' mscs ts' ds' ]] *
          [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file 
                    tinum dstbase dstname dstfile) ts' ]] *
          [[ tree_with_src Ftree srcpath [temp_fn] srcinum file 
                    dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] 
                \/
         (exists f' tinum',
         [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
         [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file
                     tinum' dstbase dstname dstfile) ts' ]] *
         [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum' 
                    f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]))) 
        \/
       (exists tinum',
          [[r = true ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
          [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file 
                          tinum' dstbase dstname dstfile) ts' ]] *
          [[ tree_with_dst Ftree srcpath [temp_fn] srcinum file 
                    dstbase dstname (dir2flatmem2 (TStree ts'!!)) ]]))
    REC:hm' RET:r
      [[ isError r ]] * any \/
      exists d sm' t mscs' dstfile',
      [[ r = OK (mscs', fsxp) ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') sm' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' (t, nil) (d, nil) ]] *
      [[ treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dstfile') (t, nil) ]]
    >>X} atomic_cp fsxp srcinum dstbase dstname mscs >> atomic_cp_recover.
Proof.
(* skipped proof tokens: 2576 *)
Admitted.
