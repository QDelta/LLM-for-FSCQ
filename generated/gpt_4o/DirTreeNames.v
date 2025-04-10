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
Require Import DirTreeDef.
Require Import DirTreePath.
Require Import DirTreePred.
Require Import DirTreeRep.
Require Import SepAuto.
Import ListNotations.
Set Implicit Arguments.
Inductive tree_names_distinct : dirtree -> Prop :=
  | TND_file : forall inum f, tree_names_distinct (TreeFile inum f)
  | TND_dir : forall inum tree_ents,
    Forall tree_names_distinct (map snd tree_ents) ->
    NoDup (map fst tree_ents) ->
    tree_names_distinct (TreeDir inum tree_ents).
Lemma rep_tree_names_distinct' : forall tree F xp m,
    (F * tree_pred xp tree)%pred m ->
    tree_names_distinct tree.
Proof.
(* skipped proof tokens: 146 *)
Admitted.
Lemma rep_tree_names_distinct : forall tree F fsxp Ftop m ilist frees ms sm,
    (F * rep fsxp Ftop tree ilist frees ms sm)%pred m ->
    tree_names_distinct tree.
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma tree_names_distinct_update_subtree : forall pn t subtree,
    tree_names_distinct t ->
    tree_names_distinct subtree ->
    tree_names_distinct (update_subtree pn subtree t).
Proof.
(* skipped proof tokens: 191 *)
Admitted.
Theorem tree_names_distinct_head : forall n a d l,
    tree_names_distinct (TreeDir n ((a, d) :: l)) ->
    tree_names_distinct (TreeDir n ([(a, d)])).
Proof.
(* skipped proof tokens: 61 *)
Admitted.
Theorem tree_names_distinct_child : forall n a d l,
    tree_names_distinct (TreeDir n ((a, d) :: l)) ->
    tree_names_distinct d.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Hint Resolve tree_names_distinct_child.
Lemma tree_names_distinct_next : forall n s d l,
    tree_names_distinct (TreeDir n ((s, d) :: l)) ->
    tree_names_distinct (TreeDir n l).
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Hint Resolve tree_names_distinct_next.
Lemma tree_names_distinct_head_not_rest : forall inum e ents name path subtree,
    tree_names_distinct (TreeDir inum (e :: ents)) ->
    find_subtree (name::path) (TreeDir inum ents) = Some subtree ->
    find_subtree (name::path) (TreeDir inum (e :: ents)) = Some subtree.
Proof.
(* skipped proof tokens: 103 *)
Admitted.
Lemma tree_names_distinct_head_name : forall inum name subtree rest,
    tree_names_distinct (TreeDir inum ((name, subtree) :: rest)) ->
    ~ In name (map fst rest).
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma tree_name_distinct_rest: forall inum x l,
        tree_names_distinct (TreeDir inum (x::l)) ->
        tree_names_distinct (TreeDir inum l).
Proof.
(* skipped proof tokens: 60 *)
Admitted.
Lemma tree_name_distinct_head: forall inum name l t,
        tree_names_distinct (TreeDir inum ((name, t)::l)) ->
        tree_names_distinct t.
Proof.
(* original proof tokens: 55 *)
(* generated proof tokens: 49 *)

intros inum name l t H.
inversion H; subst.
apply Forall_forall with (x := t) in H2.
- exact H2.
- simpl; left; reflexivity.
Qed.

Lemma tree_names_distinct_subtree : forall path tree subtree,
    tree_names_distinct tree ->
    find_subtree path tree = Some subtree ->
    tree_names_distinct subtree.
Proof.
(* skipped proof tokens: 125 *)
Admitted.
Lemma tree_names_distinct_nodup : forall dnum ents,
    tree_names_distinct (TreeDir dnum ents) ->
    NoDup (map fst ents).
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Lemma tree_names_distinct_delete_from_list : forall l n name,
    tree_names_distinct (TreeDir n l) ->
    tree_names_distinct (TreeDir n (delete_from_list name l)).
Proof.
(* skipped proof tokens: 132 *)
Admitted.
Lemma tree_names_distinct_delete_ne: forall l path name' n subtree,
    NoDup (map fst l) ->
    (~ pathname_prefix [name'] path) ->
    tree_names_distinct (TreeDir n l) ->
    find_subtree path (delete_from_dir name' (TreeDir n l)) = Some subtree ->
    tree_names_distinct subtree.
Proof.
(* skipped proof tokens: 92 *)
Admitted.
Lemma tree_names_distinct_prune_child_subtree: forall path suffix tree name subtree n l,
    tree_names_distinct tree ->
    find_subtree (path ++ suffix) tree = Some (TreeDir n l) ->
    find_subtree path (update_subtree (path++suffix) (delete_from_dir name (TreeDir n l)) tree) 
      = Some subtree ->
    tree_names_distinct subtree.
Proof.
(* skipped proof tokens: 105 *)
Admitted.
Lemma update_subtree_path_notfound: forall p tree subtree,
    tree_names_distinct tree ->
    find_subtree p tree = None ->
    update_subtree p subtree tree = tree.
Proof.
(* skipped proof tokens: 221 *)
Admitted.
Lemma find_subtree_update_subtree_ne_path : forall p1 p2 tree subtree,
    tree_names_distinct tree ->
    (~ pathname_prefix p2 p1) ->
    (~ pathname_prefix p1 p2) ->
    find_subtree p1 (update_subtree p2 subtree tree) = find_subtree p1 tree.
Proof.
(* skipped proof tokens: 540 *)
Admitted.
Lemma tree_names_distinct_prune_subtree : forall path tree path' name subtree n l,
    tree_names_distinct tree ->
    find_subtree path' tree = Some (TreeDir n l) ->
    find_subtree path (tree_prune n l path' name tree) = Some subtree ->
    tree_names_distinct subtree.
Proof.
(* skipped proof tokens: 356 *)
Admitted.
Lemma tree_names_distinct_prune_subtree' : forall inum ents base name tree,
    tree_names_distinct tree ->
    find_subtree base tree = Some (TreeDir inum ents) ->
    tree_names_distinct (tree_prune inum ents base name tree).
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma find_subtree_add_to_list_oob: forall ents dnum s name subtree d,
    tree_names_distinct (TreeDir dnum ents) ->
    s <> name ->
    find_subtree [s] (TreeDir dnum (add_to_list name subtree ents)) = Some d ->
    find_subtree [s] (TreeDir dnum ents) = Some d.
Proof.
(* skipped proof tokens: 181 *)
Admitted.
Lemma find_subtree_add_to_dir_oob: forall suffix name dnum ents subtree inum f,
     tree_names_distinct (TreeDir dnum ents) ->
     (~pathname_prefix [name] suffix) ->
     find_subtree suffix (add_to_dir name subtree (TreeDir dnum ents)) = Some (TreeFile inum f)->
     find_subtree suffix (add_to_dir name subtree (TreeDir dnum ents)) = find_subtree suffix (TreeDir dnum ents).
Proof.
(* skipped proof tokens: 147 *)
Admitted.
Lemma find_subtree_add_to_dir_oob': forall suffix name tree subtree inum f,
     tree_names_distinct tree ->
     (~pathname_prefix [name] suffix) ->
     find_subtree suffix (add_to_dir name subtree tree) = Some (TreeFile inum f)->
     find_subtree suffix (add_to_dir name subtree tree) = find_subtree suffix tree.
Proof.
(* skipped proof tokens: 65 *)
Admitted.
Lemma find_subtree_rename_oob: forall x n l n' l' dnum ents inum f srcpath srcname dstpath dstname mvtree,
    tree_names_distinct (TreeDir dnum ents) ->
    ~pathname_prefix [dstname] x ->
    find_subtree srcpath (TreeDir dnum ents) = Some (TreeDir n l) ->
    find_dirlist srcname l = Some mvtree ->
    find_subtree dstpath (tree_prune n l srcpath srcname (TreeDir dnum ents)) =
       Some (TreeDir n' l') ->
    find_subtree (dstpath ++ x) (tree_graft n' l' dstpath dstname mvtree
            (tree_prune n l srcpath srcname (TreeDir dnum ents))) = 
      Some (TreeFile inum f) ->
    find_subtree (dstpath ++ x) (TreeDir dnum ents) = Some (TreeFile inum f).
Proof.
(* skipped proof tokens: 1922 *)
Admitted.
Lemma find_subtree_rename_oob_srcname_dst: forall pathname dstpath dstname srcpath srcname n l dnum ents inum f,
    (~pathname_prefix (srcpath++[srcname]) pathname) ->
    (~pathname_prefix (dstpath++[dstname]) pathname) ->
    (~pathname_prefix dstpath pathname) ->
    tree_names_distinct (TreeDir dnum ents) ->   
    find_subtree srcpath (TreeDir dnum ents) = Some (TreeDir n l) ->
    find_subtree pathname
       (update_subtree srcpath (TreeDir n (delete_from_list srcname l))
          (TreeDir dnum ents)) = Some (TreeFile inum f) ->
    find_subtree pathname (TreeDir dnum ents) = Some (TreeFile inum f).
Proof.
(* original proof tokens: 317 *)

(* No more tactics to try *)
Admitted.

Theorem update_subtree_app : forall p0 p1 tree subtree t,
    tree_names_distinct tree ->
    find_subtree p0 tree = Some subtree ->
    update_subtree (p0 ++ p1) t tree = update_subtree p0 (update_subtree p1 t subtree) tree.
Proof.
(* skipped proof tokens: 134 *)
Admitted.
Lemma find_subtree_dir_after_update_subtree : forall base pn t num ents subtree,
    tree_names_distinct t ->
    find_subtree pn t = Some (TreeDir num ents) ->
    ~ (exists suffix : list string, pn = base ++ suffix) ->
    exists ents,
    find_subtree pn (update_subtree base subtree t) = Some (TreeDir num ents).
Proof.
(* skipped proof tokens: 200 *)
Admitted.
Lemma find_subtree_none_after_update_subtree : forall base pn t subtree,
    tree_names_distinct t ->
    find_subtree pn t = None ->
    ~ (exists suffix : list string, pn = base ++ suffix) ->
    find_subtree pn (update_subtree base subtree t) = None.
Proof.
(* skipped proof tokens: 190 *)
Admitted.
Lemma find_subtree_tree_names_distinct: forall pn t subtree,
      tree_names_distinct t ->
      find_subtree pn t = Some subtree ->
      tree_names_distinct subtree.
Proof.
(* skipped proof tokens: 109 *)
Admitted.
Lemma find_subtree_before_prune_general : forall pn t num ents base name subtree,
    tree_names_distinct t ->
    find_subtree base t = Some (TreeDir num ents) ->
    find_subtree pn (tree_prune num ents base name t) = Some subtree ->
    exists subtree',
      find_subtree pn t = Some subtree' /\
      dirtree_inum subtree = dirtree_inum subtree' /\
      dirtree_isdir subtree = dirtree_isdir subtree'.
Proof.
(* skipped proof tokens: 547 *)
Admitted.
Lemma find_subtree_before_prune : forall pn t num ents base name dnum0 ents0,
    tree_names_distinct t ->
    find_subtree base t = Some (TreeDir num ents) ->
    find_subtree pn (tree_prune num ents base name t) = Some (TreeDir dnum0 ents0) ->
    exists ents1,
    find_subtree pn t = Some (TreeDir dnum0 ents1).
Proof.
(* skipped proof tokens: 49 *)
Admitted.
Lemma find_subtree_pruned_none : forall tree base name basenum basedents,
    tree_names_distinct tree ->
    find_subtree base tree = Some (TreeDir basenum basedents) ->
    find_subtree (base ++ [name]) (tree_prune basenum basedents base name tree) = None.
Proof.
(* skipped proof tokens: 154 *)
Admitted.
Lemma update_name_twice: forall tree_elem name tree subtree subtree' dnum,
    tree_names_distinct
      (update_subtree ([name]) subtree'
         (update_subtree [] (add_to_dir name subtree (TreeDir dnum tree_elem))
            tree)) ->
    update_subtree [name] subtree' (update_subtree [] (add_to_dir name subtree (TreeDir dnum tree_elem)) tree) =
    update_subtree [] (add_to_dir name subtree' (TreeDir dnum tree_elem)) tree.
Proof.
(* skipped proof tokens: 181 *)
Admitted.
Lemma update_update_subtree_twice: forall prefix name subtree' subtree d dnum tree_elem,
    tree_names_distinct 
       (update_subtree (prefix ++ [name]) subtree'
          (update_subtree prefix
             (add_to_dir name subtree (TreeDir dnum tree_elem)) d)) ->
    update_subtree (prefix ++ [name]) subtree'
       (update_subtree prefix (add_to_dir name subtree (TreeDir dnum tree_elem)) d) =
        update_subtree prefix (add_to_dir name subtree' (TreeDir dnum tree_elem)) d.
Proof.
(* skipped proof tokens: 217 *)
Admitted.
Theorem update_subtree_tree_graft: 
    forall prefix name tree dnum tree_elem subtree subtree' F Ftop m fsxp ilist frees ms sm,
    (F * rep fsxp Ftop (update_subtree (prefix++[name]) subtree' 
                        (tree_graft dnum tree_elem prefix name subtree tree)) ilist frees ms sm)%pred m -> 
    find_subtree prefix tree = Some (TreeDir dnum tree_elem) ->
    update_subtree (prefix++[name]) subtree' (tree_graft dnum tree_elem prefix name subtree tree) = 
            (tree_graft dnum tree_elem prefix name subtree' tree).
Proof.
(* skipped proof tokens: 59 *)
Admitted.
