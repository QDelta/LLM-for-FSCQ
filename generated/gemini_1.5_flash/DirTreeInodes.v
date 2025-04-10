Require Import Bool.
Require Import Word.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import Pred.
Require Import Arith.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import AsyncDisk.
Require Import DirName.
Require Import DirTreePath.
Require Import DirTreeDef.
Require Import DirTreePred.
Require Import DirTreeRep.
Require Import DirTreeNames.
Require Import SepAuto.
Require Import GenSepN.
Import ListNotations.
Fixpoint tree_inodes t :=
    match t with
    | TreeFile inum f => [inum]
    | TreeDir inum ents => [inum] ++ (dirlist_combine tree_inodes ents)
    end.
Definition tree_inodes_distinct t := NoDup (tree_inodes t).
Hint Resolve in_or_app.
Hint Resolve in_app_or.
Hint Resolve NoDup_app_l.
Hint Resolve NoDup_app_r.
Theorem tree_inodes_distinct_child : forall n a d l,
    tree_inodes_distinct (TreeDir n ((a, d) :: l)) ->
    tree_inodes_distinct d.
Proof.
(* original proof tokens: 30 *)
intros.
eapply NoDup_app_r; eauto.
apply NoDup_app_r in H.
apply NoDup_app_r in H.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
eapply NoDup_app_r; eauto.
(* No more tactics to try *)
Admitted.

Theorem tree_inodes_distinct_head : forall n a d l,
    tree_inodes_distinct (TreeDir n ((a, d) :: l)) ->
    tree_inodes_distinct (TreeDir n ([(a,d)])).
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Theorem dirtree_update_inode_absent : forall tree inum off v,
    ~ In inum (tree_inodes tree) ->
    dirtree_update_inode tree inum off v = tree.
Proof.
(* original proof tokens: 86 *)

(* No more tactics to try *)
Admitted.

Theorem find_subtree_inum_present : forall pathname tree sub,
    find_subtree pathname tree = Some sub ->
    In (dirtree_inum sub) (tree_inodes tree).
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Hint Resolve tree_inodes_distinct_child.
Hint Resolve find_subtree_inum_present.
Lemma dirtree_update_inode_absent' : forall l inum off v,
    ~ In inum (concat (map (fun e => tree_inodes (snd e)) l)) ->
    dirlist_update (fun t' : dirtree => dirtree_update_inode t' inum off v) l = l.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_distinct_not_in_tail : forall l d n inum a,
    In inum (tree_inodes d) ->
    tree_inodes_distinct (TreeDir n ((a, d) :: l)) ->
    ~ In inum (concat (map (fun e : string * dirtree => tree_inodes (snd e)) l)).
Proof.
(* original proof tokens: 184 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_distinct_not_this_child : forall n s d l pathname inum f,
    tree_inodes_distinct (TreeDir n ((s, d) :: l)) ->
    find_subtree pathname (TreeDir n l) = Some (TreeFile inum f) ->
    ~ In inum (tree_inodes d).
Proof.
(* original proof tokens: 60 *)

(* No more tactics to try *)
Admitted.

Hint Resolve tree_inodes_distinct_not_in_tail.
Hint Resolve tree_inodes_distinct_not_this_child.
Lemma tree_inodes_distinct_next : forall n s d l,
    tree_inodes_distinct (TreeDir n ((s, d) :: l)) ->
    tree_inodes_distinct (TreeDir n l).
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

Hint Resolve tree_inodes_distinct_next.
Theorem dirtree_update_inode_update_subtree : forall pathname tree inum off f v,
    tree_inodes_distinct tree ->
    tree_names_distinct tree ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    off < length (DFData f) ->
    let f' := mk_dirfile (updN (DFData f) off v) (DFAttr f) in
    dirtree_update_inode tree inum off v =
    update_subtree pathname (TreeFile inum f') tree.
Proof.
(* original proof tokens: 223 *)

(* No more tactics to try *)
Admitted.

Theorem dirtree_update_inode_oob : forall pathname tree inum off f v,
    tree_inodes_distinct tree ->
    tree_names_distinct tree ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    ~ off < length (DFData f) ->
    dirtree_update_inode tree inum off v = tree.
Proof.
(* original proof tokens: 233 *)

(* No more tactics to try *)
Admitted.

Lemma rep_tree_inodes_distinct : forall tree F fsxp Ftop m ilist frees ms sm,
    (F * rep fsxp Ftop tree ilist frees ms sm)%pred m ->
    tree_inodes_distinct tree.
Proof.
(* original proof tokens: 162 *)

(* No more tactics to try *)
Admitted.

Lemma find_dirlist_tree_inodes: forall elem name d dnum,
    tree_names_distinct (TreeDir dnum elem) ->
    find_dirlist name elem = Some d ->
    In (dirtree_inum d) (dirlist_combine tree_inodes elem).
Proof.
(* original proof tokens: 169 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_distinct_delete: forall elem name dnum d n inum, 
    tree_names_distinct (TreeDir dnum elem) ->
    tree_inodes_distinct (TreeDir dnum elem) ->
    find_dirlist name elem = Some d ->
    dirtree_inum d = n ->
    In inum (dirlist_combine tree_inodes (delete_from_list name elem)) ->
    inum <> n.
Proof.
(* original proof tokens: 454 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_distinct_elem: forall a n l subtree,
    tree_inodes_distinct (TreeDir n l) ->
    find_subtree [a] (TreeDir n l) = Some subtree ->
    tree_inodes_distinct subtree.
Proof.
(* original proof tokens: 110 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_distinct_subtree : forall path tree subtree,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    find_subtree path tree = Some subtree ->
    tree_inodes_distinct subtree.
Proof.
(* original proof tokens: 252 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_distinct_update_subtree : forall pn t subtree subtree',
    tree_names_distinct t ->
    tree_inodes_distinct t ->
    tree_inodes_distinct subtree ->
    find_subtree pn t = Some subtree' ->
    incl (tree_inodes subtree) (tree_inodes subtree') ->
    (tree_inodes_distinct (update_subtree pn subtree t) /\
     incl (tree_inodes (update_subtree pn subtree t)) (tree_inodes t)).
Proof.
(* original proof tokens: 445 *)
split.
(* No more tactics to try *)
Admitted.

Lemma tree_inodes_distinct_update_subtree': forall pathname tree subtree d,
    tree_names_distinct tree ->
    find_subtree pathname tree = Some d ->
    incl (tree_inodes subtree) (tree_inodes (update_subtree pathname subtree tree)).
Proof.
(* original proof tokens: 234 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_in_update_subtree_child: forall pathname subtree inum tree d,
    tree_names_distinct tree ->
    In inum (tree_inodes subtree) ->
    find_subtree pathname tree = Some d ->
    In inum (tree_inodes (update_subtree pathname subtree tree)).
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma leaf_in_inodes_parent : forall path name n l subtree_base d,
    tree_names_distinct (TreeDir n l) ->
    find_subtree [name] (TreeDir n l) = Some subtree_base ->
    find_subtree path subtree_base = Some d ->
    In (dirtree_inum d) (dirlist_combine tree_inodes l).
Proof.
(* original proof tokens: 162 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_not_distinct: forall l n s f suffix,
    tree_names_distinct (TreeDir n l) ->
    tree_inodes_distinct (TreeDir n l) ->
    find_subtree (s :: suffix) (TreeDir n l) = Some f ->
    dirtree_inum (TreeDir n l) = dirtree_inum f ->
    False.
Proof.
(* original proof tokens: 83 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_in_update_subtree_oob: forall dstpath dstnum dstents tree subtree suffix inum f,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    find_subtree dstpath tree = Some (TreeDir dstnum dstents) ->
    find_subtree suffix tree = Some (TreeFile inum f) ->
    In inum (tree_inodes tree) ->
    (~ pathname_prefix dstpath suffix) ->
    In inum (tree_inodes (update_subtree dstpath subtree tree)).
Proof.
(* original proof tokens: 718 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_in_add_to_dir_oob: forall pn inum tree subtree dstname f,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    find_subtree pn tree = Some (TreeFile inum f) ->
    (~pathname_prefix [dstname] pn) ->
    In inum (tree_inodes (add_to_dir dstname subtree tree)).
Proof.
(* original proof tokens: 546 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_in_delete_from_list_oob: forall pn srcents inum f srcnum srcname,
    tree_names_distinct (TreeDir srcnum srcents) ->
    tree_inodes_distinct (TreeDir srcnum srcents) ->
    find_subtree pn (TreeDir srcnum srcents) = Some (TreeFile inum f) ->
    (~ pathname_prefix [srcname] pn) -> 
    In inum (tree_inodes (TreeDir srcnum srcents)) ->
    In inum (tree_inodes (TreeDir srcnum (delete_from_list srcname srcents))).
Proof.
(* original proof tokens: 342 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_in_delete_from_dir_oob: forall pn srcents inum f srcnum srcname,
    tree_names_distinct (TreeDir srcnum srcents) ->
    tree_inodes_distinct (TreeDir srcnum srcents) ->
    find_subtree pn (TreeDir srcnum srcents) = Some (TreeFile inum f) ->
    (~ pathname_prefix [srcname] pn) -> 
    In inum (tree_inodes (TreeDir srcnum srcents)) ->
    In inum (tree_inodes (delete_from_dir srcname (TreeDir srcnum srcents))).
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_incl_delete_from_list : forall name l,
    incl (dirlist_combine tree_inodes (delete_from_list name l))
         (dirlist_combine tree_inodes l).
Proof.
(* original proof tokens: 65 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_nodup_delete_from_list : forall name l,
    NoDup (dirlist_combine tree_inodes l) ->
    NoDup (dirlist_combine tree_inodes (delete_from_list name l)).
Proof.
(* original proof tokens: 72 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_distinct_delete_from_list : forall l n name,
    tree_inodes_distinct (TreeDir n l) ->
    tree_inodes_distinct (TreeDir n (delete_from_list name l)).
Proof.
(* original proof tokens: 73 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_find_subtree_incl : forall pathname t subtree,
    find_subtree pathname t = Some subtree ->
    incl (tree_inodes subtree) (tree_inodes t).
Proof.
(* original proof tokens: 128 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_distinct_prune: forall srcbase dnum tree_elem srcnum srcents srcname,
    tree_names_distinct (TreeDir dnum tree_elem) ->
    tree_inodes_distinct (TreeDir dnum tree_elem) ->
    find_subtree srcbase (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ->
    tree_inodes_distinct
      (tree_prune srcnum srcents srcbase srcname (TreeDir dnum tree_elem)).
Proof.
(* original proof tokens: 89 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_in_rename_oob: forall pathname' cwd srcbase srcname dstbase dstname
       inum f  dnum tree_elem srcnum srcents dstnum dstents d tree,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    (~ pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname') ->
    (~ pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname') ->
    find_subtree pathname' tree = Some (TreeFile inum f) ->
    find_subtree cwd tree = Some (TreeDir dnum tree_elem) ->
    find_subtree srcbase (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some d ->
    find_subtree dstbase
          (tree_prune srcnum srcents srcbase srcname (TreeDir dnum tree_elem)) =
        Some (TreeDir dstnum dstents) ->
    In inum
      (tree_inodes
         (update_subtree cwd
            (tree_graft dstnum dstents dstbase dstname d
               (tree_prune srcnum srcents srcbase srcname
                  (TreeDir dnum tree_elem))) tree)).
Proof.
(* original proof tokens: 3388 *)

(* No more tactics to try *)
Admitted.

Hint Resolve pathname_prefix_neq.
Lemma tree_inodes_in_delete_oob: forall pathname' base name inum f dnum dents tree,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    (~ pathname_prefix (base ++ [name]) pathname') ->
    find_subtree pathname' tree = Some (TreeFile inum f) ->
    find_subtree base tree = Some (TreeDir dnum dents) ->
    In inum
      (tree_inodes
         (update_subtree base (TreeDir dnum
            (delete_from_list name dents)) tree)).
Proof.
(* original proof tokens: 210 *)

(* No more tactics to try *)
Admitted.

Definition conflicting (p q : Prop) := (p -> ~ q) /\ (q -> ~ p).
Definition xor (p q : Prop) := (p /\ ~ q) \/ (q /\ ~ p).
Lemma NoDup_In_conflicting : forall T (l1 l2 : list T) x,
    NoDup (l1 ++ l2) ->
    conflicting (In x l1) (In x l2).
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_after_prune' : forall srcpath t srcnum srcents srcname mvtree,
    tree_names_distinct t ->
    find_subtree srcpath t = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some mvtree ->
    permutation addr_eq_dec
      (tree_inodes mvtree ++ tree_inodes (tree_prune srcnum srcents srcpath srcname t))
      (tree_inodes t).
Proof.
(* original proof tokens: 566 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_after_prune : forall srcpath t srcnum srcents srcname mvtree inum,
    tree_inodes_distinct t ->
    tree_names_distinct t ->
    find_subtree srcpath t = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some mvtree ->
    conflicting (In inum (tree_inodes mvtree))
                (In inum (tree_inodes (tree_prune srcnum srcents srcpath srcname t))).
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_after_graft' : forall dstpath t dstnum dstents dstname mvtree,
    tree_names_distinct t ->
    find_subtree dstpath t = Some (TreeDir dstnum dstents) ->
    permutation
      addr_eq_dec
      (tree_inodes (tree_graft dstnum dstents dstpath dstname mvtree t))
      ((tree_inodes mvtree) ++
       (tree_inodes (tree_prune dstnum dstents dstpath dstname t))).
Proof.
(* original proof tokens: 534 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_tree_graft_incl_count : forall dstpath t dstnum dstents dstname mvtree,
    tree_names_distinct t ->
    find_subtree dstpath t = Some (TreeDir dstnum dstents) ->
    incl_count addr_eq_dec
      (tree_inodes (tree_graft dstnum dstents dstpath dstname mvtree t))
      (tree_inodes t ++ tree_inodes mvtree).
Proof.
(* original proof tokens: 540 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_after_graft : forall dstpath t dstnum dstents dstname mvtree inum,
    NoDup (tree_inodes t ++ tree_inodes mvtree) ->
    tree_names_distinct t ->
    find_subtree dstpath t = Some (TreeDir dstnum dstents) ->
    In inum (tree_inodes (tree_graft dstnum dstents dstpath dstname mvtree t)) ->
    xor (In inum (tree_inodes mvtree))
        (In inum (tree_inodes (tree_prune dstnum dstents dstpath dstname t))).
Proof.
(* original proof tokens: 174 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_nodup_delete_from_list' : forall srcpath srcname srcents srcnum t mvtree top_extras,
    forall (Hd : tree_names_distinct t),
    find_subtree srcpath t = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some mvtree ->
    NoDup (top_extras ++ tree_inodes t) ->
    NoDup (top_extras ++ tree_inodes (tree_prune srcnum srcents srcpath srcname t) ++ tree_inodes mvtree).
Proof.
(* original proof tokens: 506 *)

(* No more tactics to try *)
Admitted.

Lemma prune_graft_preserves_inodes : forall srcpath srcname srcnum srcents
                                              dstpath dstname dstnum dstents
                                              mvtree tree_elem dnum inum,
    tree_inodes_distinct (TreeDir dnum tree_elem) ->
    tree_names_distinct (TreeDir dnum tree_elem) ->
    find_subtree srcpath (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some mvtree ->
    find_subtree dstpath (tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem)) =
      Some (TreeDir dstnum dstents) ->
    In inum (tree_inodes
      (tree_graft dstnum dstents dstpath dstname mvtree
        (tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem)))) ->
    (In inum (tree_inodes
       (update_subtree dstpath (TreeDir dstnum (delete_from_list dstname dstents))
         (tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem)))) \/
     ~ In inum (tree_inodes (tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem)))).
Proof.
(* original proof tokens: 107 *)

(* No more tactics to try *)
Admitted.

Lemma tree_inodes_incl_delete_from_dir : forall pathname dnum tree_elem name pnum pelem,
    tree_names_distinct (TreeDir dnum tree_elem) ->
    tree_inodes_distinct (TreeDir dnum tree_elem) ->
    find_subtree pathname (TreeDir dnum tree_elem) = Some (TreeDir pnum pelem) ->
    incl (tree_inodes (update_subtree pathname (delete_from_dir name (TreeDir pnum pelem)) (TreeDir dnum tree_elem)))
         (tree_inodes (TreeDir dnum tree_elem)).
Proof.
(* original proof tokens: 329 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_tree_inodes_distinct: forall pn t subtree,
      tree_inodes_distinct t ->
      find_subtree pn t = Some subtree ->
      tree_inodes_distinct subtree.
Proof.
(* original proof tokens: 110 *)

(* No more tactics to try *)
Admitted.

Lemma rep_tree_distinct_impl : forall fsxp Ftop tree ilist frees ms sm,
    rep fsxp Ftop tree ilist frees ms sm =p=> rep fsxp Ftop tree ilist frees ms sm *
      [[ tree_names_distinct tree ]] *
      [[ tree_inodes_distinct tree ]].
Proof.
(* original proof tokens: 79 *)
eapply sep_star_lift2and; eauto.
(* No more tactics to try *)
Admitted.

Theorem find_subtree_inode_pathname_unique : forall path1 path2 tree f1 f2,
    tree_inodes_distinct tree ->
    tree_names_distinct tree ->
    find_subtree path1 tree = Some f1 ->
    find_subtree path2 tree = Some f2 -> 
    dirtree_inum f1 = dirtree_inum f2 ->
    path1 = path2.
Proof.
(* original proof tokens: 824 *)

(* No more tactics to try *)
Admitted.

Theorem dirtree_update_block : forall pathname F0 tree fsxp F ilist freeblocks ms sm inum off v bn m f,
    (F0 * rep fsxp F tree ilist freeblocks ms sm)%pred (list2nmem m) ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist bn inum off ->
    (F0 * rep fsxp F (dirtree_update_inode tree inum off v) ilist freeblocks ms sm)%pred (list2nmem (updN m bn v)).
Proof.
(* original proof tokens: 363 *)

(* No more tactics to try *)
Admitted.

Theorem tree_inodes_pathname_exists : forall tree inum,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    In inum (tree_inodes tree) ->
    exists pathname subtree,
    find_subtree pathname tree = Some subtree /\ dirtree_inum subtree = inum.
Proof.
(* original proof tokens: 263 *)

(* No more tactics to try *)
Admitted.

Lemma update_subtree_same: forall pn tree subtree,
    tree_names_distinct tree ->
    find_subtree pn tree = Some subtree ->
    update_subtree pn subtree tree = tree.
Proof.
(* original proof tokens: 244 *)

(* No more tactics to try *)
Admitted.

