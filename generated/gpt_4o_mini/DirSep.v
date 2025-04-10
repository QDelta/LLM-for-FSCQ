Require Import Pred.
Require Import DirTreeDef.
Require Import DirTree.
Require Import String.
Require Import Mem.
Require Import List.
Require Import SepAuto.
Require Import BFile.
Require Import AsyncDisk.
Require Import FunctionalExtensionality.
Require Import DirTreePath.
Require Import DirTreeNames.
Require Import DirTreeInodes.
Require Import TreeCrash.
Import DIRTREE.
Import ListNotations.
Set Implicit Arguments.
Inductive flatmem_entry :=
| Nothing
| Dir : forall (inum : addr), flatmem_entry
| File : forall (inum : addr) (f : dirfile), flatmem_entry.
Definition dir2flatmem2 (d : dirtree) : @mem _ (list_eq_dec string_dec) _ :=
  fun pn => match find_subtree pn d with
  | Some (TreeFile inum f) => Some (File inum f)
  | Some (TreeDir inum _) => Some (Dir inum)
  | None => Some Nothing
  end.
Lemma dir2flatmem2_find_subtree : forall fnlist tree inum f,
  tree_names_distinct tree ->
  dir2flatmem2 tree fnlist = Some (File inum f) ->
  find_subtree fnlist tree = Some (TreeFile inum f).
Proof.
(* original proof tokens: 48 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_find_subtree_none : forall fnlist tree,
  tree_names_distinct tree ->
  dir2flatmem2 tree fnlist = Some Nothing ->
  find_subtree fnlist tree = None.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_find_subtree_dir : forall fnlist tree inum,
  tree_names_distinct tree ->
  dir2flatmem2 tree fnlist = Some (Dir inum) ->
  exists d, find_subtree fnlist tree = Some (TreeDir inum d).
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_find_subtree_ptsto : forall fnlist tree inum f F,
  tree_names_distinct tree ->
  (F * fnlist |-> File inum f)%pred (dir2flatmem2 tree) ->
  find_subtree fnlist tree = Some (TreeFile inum f).
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_find_subtree_ptsto_none : forall fnlist tree F,
  tree_names_distinct tree ->
  (F * fnlist |-> Nothing)%pred (dir2flatmem2 tree) ->
  find_subtree fnlist tree = None.
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_find_subtree_ptsto_dir : forall fnlist tree F inum,
  tree_names_distinct tree ->
  (F * fnlist |-> Dir inum)%pred (dir2flatmem2 tree) ->
  exists d, find_subtree fnlist tree = Some (TreeDir inum d).
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_find_name : forall fnlist tree inum f,
  tree_names_distinct tree ->
  dir2flatmem2 tree fnlist = Some (File inum f) ->
  find_name fnlist tree = Some (inum, false).
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_find_name_none : forall fnlist tree,
  tree_names_distinct tree ->
  dir2flatmem2 tree fnlist = Some Nothing ->
  find_name fnlist tree = None.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_find_name_ptsto : forall fnlist tree inum f F,
  tree_names_distinct tree ->
  (F * fnlist |-> File inum f)%pred (dir2flatmem2 tree) ->
  find_name fnlist tree = Some (inum, false).
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_find_name_ptsto_none : forall fnlist tree F,
  tree_names_distinct tree ->
  (F * fnlist |-> Nothing)%pred (dir2flatmem2 tree) ->
  find_name fnlist tree = None.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_update_subtree_upd : forall fnlist tree inum f f',
  tree_names_distinct tree ->
  find_subtree fnlist tree = Some (TreeFile inum f) ->
  dir2flatmem2 (update_subtree fnlist (TreeFile inum f') tree) =
  upd (dir2flatmem2 tree) fnlist (File inum f').
Proof.
(* original proof tokens: 364 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_update_subtree : forall fnlist tree inum f f' F,
  tree_names_distinct tree ->
  (F * fnlist |-> File inum f)%pred  (dir2flatmem2 tree) ->
  (F * fnlist |-> File inum f')%pred (dir2flatmem2 (update_subtree fnlist (TreeFile inum f') tree)).
Proof.
(* original proof tokens: 53 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_graft_upd : forall tree inum inum' f f' basenum basedents base name,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (find_subtree (base++[name]) tree = Some (TreeFile inum f) \/
   find_subtree (base++[name]) tree = None) ->
  dir2flatmem2 (tree_graft basenum basedents base name (TreeFile inum' f') tree) =
  upd (dir2flatmem2 tree) (base++[name]) (File inum' f').
Proof.
(* original proof tokens: 540 *)

(* No more tactics to try *)
Admitted.

Theorem dirents2mem2_graft_file_replace : forall (F: @pred _ (@list_eq_dec string string_dec) _)
      tree name inum f inum' f' basenum basedents base,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (F * (base ++ [name]) |-> File inum' f')%pred (dir2flatmem2 tree) -> 
  (F * (base ++ [name]) |-> File inum f)%pred (dir2flatmem2 (tree_graft basenum basedents base name (TreeFile inum f) tree)).
Proof.
(* original proof tokens: 55 *)
eapply sep_star_lift_apply.
eapply sep_star_lift_apply.
eapply sep_star_lift_apply.
eapply sep_star_lift_apply.
eapply sep_star_lift_apply.
eapply sep_star_lift_apply; try eapply sep_star_lift_apply.
eapply sep_star_lift_apply.
eapply sep_star_lift_apply.
eapply sep_star_lift_apply.
eapply sep_star_lift_apply.
eapply sep_star_lift_apply.
eapply sep_star_lift_apply.
(* No more tactics to try *)
Admitted.

Theorem dirents2mem2_graft_file_none : forall (F: @pred _ (@list_eq_dec string string_dec) _)
      tree name inum f basenum basedents base,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (F * (base ++ [name]) |-> Nothing)%pred (dir2flatmem2 tree) -> 
  (F * (base ++ [name]) |-> File inum f)%pred (dir2flatmem2 (tree_graft basenum basedents base name (TreeFile inum f) tree)).
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_prune_delete : forall tree inum f basenum basedents base name,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (find_subtree (base++[name]) tree = Some (TreeFile inum f) \/
   find_subtree (base++[name]) tree = None) ->
  dir2flatmem2 (tree_prune basenum basedents base name tree) =
  upd (dir2flatmem2 tree) (base++[name]) Nothing.
Proof.
(* original proof tokens: 541 *)

(* No more tactics to try *)
Admitted.

Theorem dirents2mem2_prune_file : forall (F: @pred _ (@list_eq_dec string string_dec) _)
      tree name inum f basenum basedents base,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (F * (base ++ [name]) |-> File inum f)%pred (dir2flatmem2 tree) ->
  (F * (base ++ [name]) |-> Nothing)%pred (dir2flatmem2 (tree_prune basenum basedents base name tree)).
Proof.
(* original proof tokens: 54 *)

(* No more tactics to try *)
Admitted.

Theorem dirents2mem_update_subtree_upd : forall base subtree pn v subtree0 t,
  tree_names_distinct t ->
  find_subtree base t = Some subtree0 ->
  dir2flatmem2 subtree = upd (dir2flatmem2 subtree0) pn v ->
  dir2flatmem2 (update_subtree base subtree t) = upd (dir2flatmem2 t) (base ++ pn) v.
Proof.
(* original proof tokens: 245 *)

(* No more tactics to try *)
Admitted.

Theorem dirents2mem2_update_subtree_one_name : forall t base pn subtree_old subtree_new F v0 v',
  (F * (base ++ pn) |-> v0)%pred (dir2flatmem2 t) ->
  dir2flatmem2 subtree_new = upd (dir2flatmem2 subtree_old) pn v' ->
  tree_names_distinct t ->
  find_subtree base t = Some subtree_old ->
  (F * (base ++ pn) |-> v')%pred (dir2flatmem2 (update_subtree base subtree_new t)).
Proof.
(* original proof tokens: 35 *)
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
apply exists_one.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
flatten.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
apply pimpl_exists_l; intros.
eapply pimpl_trans.
apply pimpl_exists_l; intros.
(* Reached max number of model calls *)
Admitted.

Lemma dirents2mem2_not_prefix : forall t F pn1 i1 f1 pn2 i2 f2,
  tree_names_distinct t ->
  (F * pn1 |-> File i1 f1 * pn2 |-> File i2 f2)%pred (dir2flatmem2 t) ->
  ~ pathname_prefix pn1 pn2.
Proof.
(* original proof tokens: 202 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_delete_file: forall (F: @pred _ (@list_eq_dec string string_dec) _)
     tree name inum f basenum basedents base,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (F * (base++[name])%list |-> File inum f)%pred (dir2flatmem2 tree) ->
  (F * (base++[name])%list |-> Nothing)%pred (dir2flatmem2 (update_subtree base (TreeDir basenum (delete_from_list name basedents)) tree)).
Proof.
(* original proof tokens: 81 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_rename: forall Ftree cwd srcbase srcname dstbase dstname
      dstnum0 dstents subtree srcnum0 srcents srcnum srcfile dstnum dstfile 
      dnum tree_elem tree,
  tree_names_distinct tree ->
  tree_inodes_distinct tree ->
  ((Ftree ✶ (cwd ++ srcbase ++ [srcname]) |-> File srcnum srcfile)
    ✶ (cwd ++ dstbase ++ [dstname]) |-> File dstnum dstfile)%pred 
      (dir2flatmem2 tree) ->
  find_subtree cwd tree = Some (TreeDir dnum tree_elem) ->
  find_subtree srcbase (TreeDir dnum tree_elem) = Some (TreeDir srcnum0 srcents) ->
  find_dirlist srcname srcents = Some subtree ->
  find_subtree dstbase
          (tree_prune srcnum0 srcents srcbase srcname (TreeDir dnum tree_elem)) =
        Some (TreeDir dstnum0 dstents) ->
  ((Ftree ✶ (cwd ++ srcbase ++ [srcname]) |-> Nothing)
   ✶ (cwd ++ dstbase ++ [dstname]) |-> File srcnum srcfile)%pred
    (dir2flatmem2
      (update_subtree cwd
        (tree_graft dstnum0 dstents dstbase dstname subtree
         (tree_prune srcnum0 srcents srcbase srcname
            (TreeDir dnum tree_elem))) tree)).
Proof.
(* original proof tokens: 439 *)
unfold dir2flatmem2.
intros.
repeat match goal with
| [ H: context[find_subtree _ (TreeDir _ _)] |- _ ] =>
    destruct H; [ | clear H ]
end.
unfold dir2flatmem2 in *.
simpl in *.
clear.
(* No more tactics to try *)
Admitted.

Global Opaque dir2flatmem2.
