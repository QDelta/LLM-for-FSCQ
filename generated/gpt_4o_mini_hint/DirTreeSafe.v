Require Import Bool.
Require Import Word.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import Pred.
Require Import Arith.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import AsyncDisk.
Require Import SepAuto.
Require Import GenSepN.
Require Import GenSepAuto.
Require Import DirTreePath.
Require Import DirTreeDef.
Require Import DirTreePred.
Require Import DirTreeRep.
Require Import DirTreeNames.
Require Import DirTreeInodes.
Import ListNotations.
Set Implicit Arguments.
Definition dirtree_safe ilist1 free1 tree1 ilist2 free2 tree2 :=
    BFILE.ilist_safe ilist1 free1 ilist2 free2 /\
    forall inum off bn pathname f,
      find_subtree pathname tree2 = Some (TreeFile inum f) ->
      BFILE.block_belong_to_file ilist2 bn inum off ->
      ((BFILE.block_belong_to_file ilist1 bn inum off /\
        exists pathname' f', find_subtree pathname' tree1 = Some (TreeFile inum f')) \/
       BFILE.block_is_unused free1 bn).
Theorem dirtree_safe_refl : forall i f t,
    dirtree_safe i f t i f t.
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Theorem dirtree_safe_trans : forall i1 f1 t1 i2 t2 f2 i3 t3 f3,
    dirtree_safe i1 f1 t1 i2 f2 t2 ->
    dirtree_safe i2 f2 t2 i3 f3 t3 ->
    dirtree_safe i1 f1 t1 i3 f3 t3.
(* hint proof tokens: 88 *)
Proof.
    unfold dirtree_safe; intros.
    intuition.
    eapply BFILE.ilist_safe_trans; eauto.
    edestruct H3; eauto.
    - intuition; repeat deex. 
      edestruct H2; eauto.
    - right.
      unfold BFILE.ilist_safe in *.
      unfold BFILE.block_is_unused in *; eauto.
      intuition.
  Qed.
Lemma dirtree_safe_file : forall ilist frees inum f f',
    dirtree_safe ilist frees (TreeFile inum f) ilist frees (TreeFile inum f').
(* hint proof tokens: 62 *)
Proof.
    unfold dirtree_safe; intuition.
    apply BFILE.ilist_safe_refl.
    left; split; auto.
    exists pathname. eexists.
    destruct pathname; simpl in *; try congruence.
    inversion H.
    subst; eauto.
  Qed.
Lemma dirtree_safe_ilist_trans : forall ilist frees ilist' frees' tree tree',
    dirtree_safe ilist frees tree ilist frees tree' ->
    BFILE.ilist_safe ilist frees ilist' frees' ->
    dirtree_safe ilist frees tree ilist' frees' tree'.
(* hint proof tokens: 56 *)
Proof.
    unfold dirtree_safe, BFILE.ilist_safe; intuition.
    specialize (H3 _ _ _ H5); intuition.
    specialize (H4 _ _ _ H6); intuition.
    eapply H2; eauto.
  Qed.
Lemma dirtree_safe_file_trans : forall ilist frees ilist' frees' inum f f',
    BFILE.ilist_safe ilist frees ilist' frees' ->
    dirtree_safe ilist frees (TreeFile inum f) ilist' frees' (TreeFile inum f').
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Theorem dirlist_safe_subtree : forall pathname tree
                                        ilist  freeblocks  subtree
                                        ilist' freeblocks' subtree',
    find_subtree pathname tree = Some subtree ->
    dirtree_safe ilist  freeblocks  subtree
                 ilist' freeblocks' subtree' ->
    dirtree_safe ilist  freeblocks  tree
                 ilist' freeblocks' (update_subtree pathname subtree' tree).
(* hint proof tokens: 151 *)
Proof.
    unfold dirtree_safe; intuition.
    destruct (pathname_decide_prefix pathname pathname0); repeat deex.
    - edestruct H2; eauto.
      eapply find_subtree_helper1. 2: eauto. eauto.
      left; intuition. repeat deex.
      do 2 eexists.
      erewrite find_subtree_app; eauto.
    - clear H2.
      unfold BFILE.ilist_safe in H0.
      destruct H1.
      specialize (H2 _ _ _ H3).
      intuition.
      left.
      intuition.
      exists pathname0; eexists.
      erewrite <- find_subtree_update_subtree_oob'; eauto.
  Qed.
Theorem dirtree_update_safe_inum : forall ilist_newest free_newest tree_newest pathname f tree fsxp F F0 ilist freeblocks ms sm v bn inum off m flag,
    find_subtree pathname tree_newest = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist_newest bn inum off ->
    dirtree_safe ilist (BFILE.pick_balloc freeblocks flag) tree ilist_newest free_newest tree_newest ->
    (F0 * rep fsxp F tree ilist freeblocks ms sm)%pred (list2nmem m) ->
    exists tree',
    (F0 * rep fsxp F tree' ilist freeblocks ms sm)%pred (list2nmem (updN m bn v)) /\
    (tree' = tree \/
     exists pathname' f', find_subtree pathname' tree = Some (TreeFile inum f') /\
     tree' = dirtree_update_inode tree inum off v).
(* hint proof tokens: 110 *)
Proof.
    intros.
    unfold dirtree_safe, BFILE.ilist_safe in H1.
    intuition.
    specialize (H4 _ _ _ _ _ H H0).
    intuition; repeat deex.
    - 
      eexists; split.
      2: right; intuition.
      eapply dirtree_update_block; eauto.
      eauto.
    - 
      eexists; split.
      2: left; reflexivity.
      eapply dirtree_update_free; eauto.
  Qed.
Theorem dirtree_update_safe_pathname :
    forall ilist_newest free_newest tree_newest pathname f tree fsxp F F0 ilist freeblocks ms sm v bn inum off m flag,
    find_subtree pathname tree_newest = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist_newest bn inum off ->
    dirtree_safe ilist (BFILE.pick_balloc freeblocks flag) tree ilist_newest free_newest tree_newest ->
    (F0 * rep fsxp F tree ilist freeblocks ms sm)%pred (list2nmem m) ->
    exists tree',
    (F0 * rep fsxp F tree' ilist freeblocks ms sm)%pred (list2nmem (updN m bn v)) /\
    (tree' = tree \/
     exists pathname' f', find_subtree pathname' tree = Some (TreeFile inum f') /\
     let f'new := mk_dirfile (updN (DFData f') off v) (DFAttr f') in
     tree' = update_subtree pathname' (TreeFile inum f'new) tree).
Proof.
(* original proof tokens: 242 *)

(* No more tactics to try *)
Admitted.

Theorem dirtree_update_safe_pathname_pred :
    forall ilist_newest free_newest tree_newest pathname f tree fsxp F F0 ilist freeblocks ms sm v bn inum off m flag,
    (F0 * rep fsxp F tree ilist freeblocks ms sm)%pred (list2nmem m) ->
    dirtree_safe ilist (BFILE.pick_balloc freeblocks flag) tree ilist_newest free_newest tree_newest ->
    BFILE.block_belong_to_file ilist_newest bn inum off ->
    find_subtree pathname tree_newest = Some (TreeFile inum f) ->
    (F0 * rep fsxp F tree ilist freeblocks ms sm \/
     exists pathname' f',
     [[ find_subtree pathname' tree = Some (TreeFile inum f') ]] *
     let f'new := mk_dirfile (updN (DFData f') off v) (DFAttr f') in
     let tree' := update_subtree pathname' (TreeFile inum f'new) tree in
     F0 * rep fsxp F tree' ilist freeblocks ms sm)%pred (list2nmem (updN m bn v)).
Proof.
(* original proof tokens: 54 *)

(* No more tactics to try *)
Admitted.

Theorem dirlist_safe_mkdir : forall ilist freeblocks ilist' freeblocks'
                                      dnum tree_elem name inum,
    BFILE.ilist_safe ilist freeblocks ilist' freeblocks' ->
    dirtree_safe ilist freeblocks (TreeDir dnum tree_elem)
                 ilist' freeblocks' (TreeDir dnum ((name, TreeDir inum []) :: tree_elem)).
Proof.
(* original proof tokens: 102 *)
intros.
unfold dirtree_safe in *; intuition.
eapply BFILE.block_belong_to_file_bfdata_length in H1.
(* No more tactics to try *)
Admitted.

Theorem dirlist_safe_mkfile : forall ilist IFs freeblocks ilist' freeblocks' frees msc ms icache dblocks
                                      dnum tree_elem name inum m flist' bxp ixp F Fm,
   (Fm * BFILE.rep bxp IFs ixp flist' ilist' frees msc ms icache dblocks)%pred m ->
   (F * inum |-> BFILE.bfile0 )%pred (list2nmem flist') ->
    BFILE.ilist_safe ilist  freeblocks ilist' freeblocks' ->
    tree_names_distinct (TreeDir dnum tree_elem) ->
    ~ In name (map fst tree_elem) ->
    dirtree_safe ilist  freeblocks (TreeDir dnum tree_elem)
                 ilist' freeblocks' (TreeDir dnum (tree_elem ++ [(name, TreeFile inum dirfile0)])).
(* hint proof tokens: 379 *)
Proof.
    unfold dirtree_safe, BFILE.ilist_safe; intuition.
    denote (forall _, _ ) as Hx; denote (BFILE.block_belong_to_file) as Hy.
    specialize (Hx _ _ _ Hy); destruct Hx.
    2: right; intuition.  
    destruct pathname.
    simpl in *; congruence.

    denote tree_names_distinct as Hz; inversion Hz; subst.
    apply find_subtree_ents_rev_nodup in H1.
    rewrite rev_app_distr in H1; simpl in *.
    destruct (string_dec name s); subst; eauto.

    - 
      exfalso.
      destruct pathname; simpl in *; try congruence.

      inversion H1; subst.
      unfold BFILE.rep in H; destruct_lift H.
      unfold BFILE.block_belong_to_file in Hy; intuition subst.
      extract.
      eapply list2nmem_sel in H0; rewrite <- H0 in *.
      setoid_rewrite ListPred.listmatch_length_pimpl in H at 2.
      destruct_lift H; rewrite map_length in *.
      denote (0 = _) as Heq; rewrite <- Heq in *.
      denote (off < _) as Hlt; inversion Hlt.
    - 
      left; intuition.
      do 2 eexists.
      rewrite <- rev_involutive with (l := tree_elem).
      apply find_subtree_ents_rev_nodup.
      rewrite map_rev.
      apply NoDup_rev_1; auto.
      eassign (s :: pathname); simpl; eauto.

    - rewrite map_app; simpl.
      apply NoDup_app_comm; simpl.
      constructor; auto.

    Unshelve. all: eauto; exact unit.
  Qed.
Lemma dirtree_safe_update_subtree : forall ilist frees tree ilist' frees' tree' inum pathname f f',
    dirtree_safe ilist frees tree ilist' frees' tree' ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    dirtree_safe ilist frees (update_subtree pathname (TreeFile inum f') tree) ilist' frees' tree'.
Proof.
(* original proof tokens: 107 *)

(* No more tactics to try *)
Admitted.

Lemma dirlist_safe_delete : forall ilist frees ilist' frees' dnum name ents,
    tree_names_distinct (TreeDir dnum ents) ->
    BFILE.ilist_safe ilist frees ilist' frees' ->
    dirtree_safe ilist frees (TreeDir dnum ents)
                 ilist' frees' (TreeDir dnum (delete_from_list name ents)).
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma dirtree_safe_rename_dest_none : 
    forall ilist1 ilist2 frees1 frees2 srcpath srcname dstpath dstname dnum ents n l n' l' mvtree,
    let pruned  := tree_prune n l srcpath srcname (TreeDir dnum ents) in
    let grafted := tree_graft n' l' dstpath dstname mvtree pruned in
    tree_names_distinct (TreeDir dnum ents) ->
    tree_inodes_distinct (TreeDir dnum ents) ->
    find_subtree srcpath (TreeDir dnum ents) = Some (TreeDir n l) ->
    find_subtree dstpath pruned = Some (TreeDir n' l') ->
    ~ In dstname (map fst l') ->
    find_dirlist srcname l = Some mvtree ->
    BFILE.ilist_safe ilist1 frees1 ilist2 frees2 ->
    dirtree_safe ilist1 frees1 (TreeDir dnum ents) ilist2 frees2 grafted.
(* hint proof tokens: 545 *)
Proof.
    cbn; intros.
    eapply dirtree_safe_ilist_trans; eauto.
    unfold dirtree_safe; intuition.
    apply BFILE.ilist_safe_refl.
    left; split; auto.

    destruct (pathname_decide_prefix (dstpath ++ [dstname]) pathname).
    - repeat deex.
      exists (srcpath ++ [srcname] ++ suffix); exists f.
      denote tree_graft as Hx.
      rewrite <- app_assoc in Hx.
      erewrite find_subtree_app in Hx by (
        erewrite <- tree_graft_not_in_dirents by auto;
        eapply find_update_subtree; eauto).

      erewrite find_subtree_app by eauto.
      erewrite find_subtree_app.

      2: apply find_dirlist_find_subtree_helper; eauto.
      erewrite find_subtree_app in Hx; eauto.
      apply find_subtree_leaf_in.
      apply in_app_iff.
      right; simpl; auto.
      rewrite map_app; apply NoDup_app_comm; simpl.
      constructor; auto.

      eapply tree_names_distinct_nodup.
      eapply tree_names_distinct_prune_subtree; eauto.
      eapply tree_names_distinct_nodup.
      eapply tree_names_distinct_subtree; eauto.

    - exists pathname, f.
      destruct (pathname_decide_prefix dstpath pathname).
      + 
        deex.
        eapply find_subtree_rename_oob; eauto.
        intro.
        eapply H8.
        unfold pathname_prefix in H9.
        deex.
        exists suffix0.
        rewrite app_assoc; eauto. 
      + 
        apply find_subtree_update_subtree_oob' in H6; auto.
        unfold tree_prune, delete_from_dir in H6.
        destruct (pathname_decide_prefix (srcpath++[srcname]) pathname); repeat deex.
        * 
          exfalso.
          erewrite <- app_assoc in H6.
          erewrite find_update_subtree_suffix in H6; eauto.
          rewrite <- cons_app in H6.
          rewrite find_subtree_delete_same' in H6; try congruence.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
        * 
          erewrite find_subtree_rename_oob_srcname_dst.
          3: eapply pathname_prefix_neq with (path' := (dstpath++[dstname])); eauto.
          all: eauto.
  Qed.
Lemma dirtree_safe_rename_dest_exists : 
    forall ilist1 ilist2 ilist3 frees1 frees2 frees3
           srcpath srcname dstpath dstname dnum ents n l n' l' mvtree,
    let pruned  := tree_prune n l srcpath srcname (TreeDir dnum ents) in
    let deleted := update_subtree dstpath (TreeDir n' (delete_from_list dstname l')) pruned in
    let grafted := tree_graft n' l' dstpath dstname mvtree pruned in
    tree_names_distinct (TreeDir dnum ents) ->
    tree_inodes_distinct (TreeDir dnum ents) ->
    find_subtree srcpath (TreeDir dnum ents) = Some (TreeDir n l) ->
    find_subtree dstpath pruned = Some (TreeDir n' l') ->
    find_dirlist srcname l = Some mvtree ->
    dirtree_safe ilist1 frees1 pruned ilist2 frees2 deleted ->
    BFILE.ilist_safe ilist2 frees2 ilist3 frees3 ->
    dirtree_safe ilist1 frees1 (TreeDir dnum ents) ilist3 frees3 grafted.
Proof.
(* original proof tokens: 511 *)

(* No more tactics to try *)
Admitted.

Lemma dirtree_safe_dupdate: forall old_tree old_free old_ilist tree ilist freelist inum f p off v,
    tree_names_distinct tree ->
    dirtree_safe old_ilist old_free old_tree ilist freelist tree ->
    find_subtree p tree = Some (TreeFile inum f) ->
    dirtree_safe old_ilist old_free old_tree ilist freelist
      (update_subtree p (TreeFile inum
        {| DFData := (DFData f) ⟦ off := v ⟧;
           DFAttr := DFAttr f |}) tree).
(* hint proof tokens: 281 *)
Proof.
    unfold dirtree_safe; intuition.
    destruct (pathname_decide_prefix pathname p); repeat deex.
    {
      destruct suffix; try rewrite app_nil_r in *.
      - erewrite find_update_subtree in H0 by eauto. inversion H0; subst. eauto.
      - case_eq (find_subtree pathname tree); intros. destruct d.
        + erewrite find_subtree_app in H1 by eauto; simpl in *; congruence.
        + erewrite find_subtree_app in H1 by eauto.
          erewrite update_subtree_app in H0 by eauto.
          erewrite find_update_subtree in H0 by eauto.
          simpl in *; congruence.
        + erewrite find_subtree_app_none in H1 by eauto; congruence.
    }

    destruct (pathname_decide_prefix p pathname); repeat deex.
    {
      exfalso.
      destruct suffix; try rewrite app_nil_r in *.
      apply H5. exists nil. rewrite app_nil_r; auto.
      erewrite find_subtree_app in H0.
      2: erewrite find_update_subtree; eauto.
      simpl in *; congruence.
    }

    rewrite find_subtree_update_subtree_ne_path in H0; eauto.
  Qed.
