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
(* skipped proof tokens: 27 *)
Admitted.
Theorem dirtree_safe_trans : forall i1 f1 t1 i2 t2 f2 i3 t3 f3,
    dirtree_safe i1 f1 t1 i2 f2 t2 ->
    dirtree_safe i2 f2 t2 i3 f3 t3 ->
    dirtree_safe i1 f1 t1 i3 f3 t3.
Proof.
(* original proof tokens: 88 *)

(* No more tactics to try *)
Admitted.

Lemma dirtree_safe_file : forall ilist frees inum f f',
    dirtree_safe ilist frees (TreeFile inum f) ilist frees (TreeFile inum f').
Proof.
(* skipped proof tokens: 62 *)
Admitted.
Lemma dirtree_safe_ilist_trans : forall ilist frees ilist' frees' tree tree',
    dirtree_safe ilist frees tree ilist frees tree' ->
    BFILE.ilist_safe ilist frees ilist' frees' ->
    dirtree_safe ilist frees tree ilist' frees' tree'.
Proof.
(* skipped proof tokens: 56 *)
Admitted.
Lemma dirtree_safe_file_trans : forall ilist frees ilist' frees' inum f f',
    BFILE.ilist_safe ilist frees ilist' frees' ->
    dirtree_safe ilist frees (TreeFile inum f) ilist' frees' (TreeFile inum f').
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Theorem dirlist_safe_subtree : forall pathname tree
                                        ilist  freeblocks  subtree
                                        ilist' freeblocks' subtree',
    find_subtree pathname tree = Some subtree ->
    dirtree_safe ilist  freeblocks  subtree
                 ilist' freeblocks' subtree' ->
    dirtree_safe ilist  freeblocks  tree
                 ilist' freeblocks' (update_subtree pathname subtree' tree).
Proof.
(* skipped proof tokens: 151 *)
Admitted.
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
Proof.
(* skipped proof tokens: 110 *)
Admitted.
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
(* skipped proof tokens: 242 *)
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
(* skipped proof tokens: 54 *)
Admitted.
Theorem dirlist_safe_mkdir : forall ilist freeblocks ilist' freeblocks'
                                      dnum tree_elem name inum,
    BFILE.ilist_safe ilist freeblocks ilist' freeblocks' ->
    dirtree_safe ilist freeblocks (TreeDir dnum tree_elem)
                 ilist' freeblocks' (TreeDir dnum ((name, TreeDir inum []) :: tree_elem)).
Proof.
(* skipped proof tokens: 102 *)
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
Proof.
(* skipped proof tokens: 379 *)
Admitted.
Lemma dirtree_safe_update_subtree : forall ilist frees tree ilist' frees' tree' inum pathname f f',
    dirtree_safe ilist frees tree ilist' frees' tree' ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    dirtree_safe ilist frees (update_subtree pathname (TreeFile inum f') tree) ilist' frees' tree'.
Proof.
(* skipped proof tokens: 107 *)
Admitted.
Lemma dirlist_safe_delete : forall ilist frees ilist' frees' dnum name ents,
    tree_names_distinct (TreeDir dnum ents) ->
    BFILE.ilist_safe ilist frees ilist' frees' ->
    dirtree_safe ilist frees (TreeDir dnum ents)
                 ilist' frees' (TreeDir dnum (delete_from_list name ents)).
Proof.
(* skipped proof tokens: 69 *)
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
Proof.
(* skipped proof tokens: 545 *)
Admitted.
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
(* skipped proof tokens: 511 *)
Admitted.
Lemma dirtree_safe_dupdate: forall old_tree old_free old_ilist tree ilist freelist inum f p off v,
    tree_names_distinct tree ->
    dirtree_safe old_ilist old_free old_tree ilist freelist tree ->
    find_subtree p tree = Some (TreeFile inum f) ->
    dirtree_safe old_ilist old_free old_tree ilist freelist
      (update_subtree p (TreeFile inum
        {| DFData := (DFData f) ⟦ off := v ⟧;
           DFAttr := DFAttr f |}) tree).
Proof.
(* skipped proof tokens: 281 *)
Admitted.
