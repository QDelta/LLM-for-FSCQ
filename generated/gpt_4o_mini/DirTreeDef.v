Require Import Bool.
Require Import Word.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import Pred.
Require Import Arith.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import AsyncDisk.
Require Import DirTreePath.
Import ListNotations.
Set Implicit Arguments.
Definition attrtype := INODE.iattr.
Definition datatype := valuset.
Record dirfile := mk_dirfile {
    DFData : list datatype;
    DFAttr : attrtype
  }.
Definition dirfile0 := mk_dirfile nil INODE.iattr0.
Inductive dirtree :=
  | TreeFile : addr -> dirfile -> dirtree
  | TreeDir  : addr -> list (string * dirtree) -> dirtree.
Definition dirtree_inum (dt : dirtree) :=
    match dt with
    | TreeFile inum _ => inum
    | TreeDir  inum _ => inum
    end.
Definition dirtree_isdir (dt : dirtree) :=
    match dt with
    | TreeFile _ _ => false
    | TreeDir  _ _ => true
    end.
Definition dirtree_dirents (dt : dirtree) :=
    match dt with
    | TreeFile _ _ => nil
    | TreeDir  _ ents => ents
    end.
Definition dirtree_file (dt : dirtree) :=
    match dt with
    | TreeFile _ f => f
    | TreeDir  _ _ => dirfile0
    end.
Definition synced_dirfile f := mk_dirfile (Array.synced_list (map fst (DFData f))) (DFAttr f).
Definition dirfile_to_bfile f c := BFILE.mk_bfile (DFData f) (DFAttr f) c.
Definition find_subtree_helper {T} (rec : dirtree -> option T) name
                                 (dirent : string * dirtree)
                                 (accum : option T) :=
    let (ent_name, ent_item) := dirent in
    if string_dec ent_name name then rec ent_item else accum.
Fixpoint find_subtree (fnlist : list string) (tree : dirtree) :=
    match fnlist with
    | nil => Some tree
    | name :: suffix =>
      match tree with
      | TreeFile _ _ => None
      | TreeDir _ dirents =>
        fold_right (find_subtree_helper (find_subtree suffix) name) None dirents
      end
    end.
Definition find_name (fnlist : list string) (tree : dirtree) :=
    match find_subtree fnlist tree with
    | None => None
    | Some subtree =>
      match subtree with
      | TreeFile inum _ => Some (inum, false)
      | TreeDir inum _ => Some (inum, true)
      end
    end.
Fixpoint find_dirlist name (l : list (string * dirtree)) :=
    match l with
    | nil => None
    | (n, sub) :: rest =>
        if string_dec n name then Some sub else find_dirlist name rest
    end.
Definition update_subtree_helper (rec : dirtree -> dirtree)
                                   name
                                   (dirent : string * dirtree) :=
    let (ent_name, ent_tree) := dirent in
    if string_dec ent_name name then (ent_name, rec ent_tree) else dirent.
Fixpoint update_subtree (fnlist : list string) (subtree : dirtree) (tree : dirtree) :=
    match fnlist with
    | nil => subtree
    | name :: rest =>
      match tree with
      | TreeFile _ _ => tree
      | TreeDir inum ents =>
        TreeDir inum (map (update_subtree_helper (update_subtree rest subtree) name) ents)
      end
    end.
Fixpoint delete_from_list (name : string) (ents : list (string * dirtree)) :=
    match ents with
    | nil => nil
    | hd :: rest =>
      let (ent_name, ent_item) := hd in
      if string_dec ent_name name then
        rest
      else
        hd :: delete_from_list name rest
    end.
Definition delete_from_dir (name : string) tree :=
    match tree with
    | TreeFile _ _ => tree
    | TreeDir inum ents => TreeDir inum (delete_from_list name ents)
    end.
Fixpoint add_to_list (name : string) (item : dirtree) (ents : list (string * dirtree)) :=
    match ents with
    | nil => (name, item) :: nil
    | (ent_name, ent_item) :: rest =>
      if string_dec ent_name name then
        (name, item) :: rest
      else
        (ent_name, ent_item) :: add_to_list name item rest
    end.
Definition add_to_dir (name : string) (item : dirtree) tree :=
    match tree with
    | TreeFile _ _ => tree
    | TreeDir inum ents => TreeDir inum (add_to_list name item ents)
    end.
Definition tree_prune snum sents srcpath srcname tree :=
    let new := delete_from_dir srcname (TreeDir snum sents) in
    update_subtree srcpath new tree.
Definition tree_graft dnum dents dstpath dstname subtree tree :=
    let new := add_to_dir dstname subtree (TreeDir dnum dents) in
    update_subtree dstpath new tree.
Lemma update_subtree_notfound : forall name l f,
    ~ In name (map fst l) ->
    map (update_subtree_helper f name) l = l.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_ents_not_in : forall T ents name acc (rec : _ -> option T),
    ~ In name (map fst ents) ->
    fold_right (find_subtree_helper rec name) acc ents = acc.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_ents_rev_nodup : forall path ents dnum inum f,
    NoDup (map fst ents) ->
    find_subtree path (TreeDir dnum ents) = Some (TreeFile inum f) ->
    find_subtree path (TreeDir dnum (rev ents)) = Some (TreeFile inum f).
Proof.
(* original proof tokens: 102 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_nil: forall pn n,
    pn <> nil ->
    find_subtree pn (TreeDir n []) = None.
Proof.
(* original proof tokens: 25 *)
(* generated proof tokens: 29 *)

simpl; intros. 
unfold find_subtree. 
destruct pn; try contradiction.
reflexivity.
Qed.

Theorem find_subtree_app : forall p0 p1 tree subtree,
    find_subtree p0 tree = Some subtree ->
    find_subtree (p0 ++ p1) tree = find_subtree p1 subtree.
Proof.
(* original proof tokens: 67 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_extend: forall p1 p2 tree subtree,
      find_subtree p1 tree = Some subtree ->
      find_subtree p2 subtree = find_subtree (p1++p2) tree.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Theorem find_subtree_app_none : forall p0 p1 tree,
    find_subtree p0 tree = None ->
    find_subtree (p0 ++ p1) tree = None.
Proof.
(* original proof tokens: 67 *)

(* No more tactics to try *)
Admitted.

Theorem find_subtree_update_subtree_oob : forall base pn tree subtree inum f,
    (~ exists suffix, pn = base ++ suffix) ->
    find_subtree pn tree = Some (TreeFile inum f) ->
    find_subtree pn (update_subtree base subtree tree) = Some (TreeFile inum f).
Proof.
(* original proof tokens: 192 *)

(* No more tactics to try *)
Admitted.

Theorem find_subtree_update_subtree_oob' : forall base pn tree subtree inum f,
    (~ exists suffix, pn = base ++ suffix) ->
    find_subtree pn (update_subtree base subtree tree) = Some (TreeFile inum f) ->
    find_subtree pn tree = Some (TreeFile inum f).
Proof.
(* original proof tokens: 203 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_update_subtree_oob_general : forall base pn tree subtree subtree',
    (~ exists suffix, pn = base ++ suffix) ->
    find_subtree pn (update_subtree base subtree tree) = Some subtree' ->
    exists subtree'',
      find_subtree pn tree = Some subtree'' /\
      dirtree_inum subtree'' = dirtree_inum subtree' /\
      dirtree_isdir subtree'' = dirtree_isdir subtree'.
Proof.
(* original proof tokens: 219 *)
firstorder.
(* No more tactics to try *)
Admitted.

Theorem find_subtree_helper1 : forall pathname suffix tree subtree subtree' r,
    find_subtree pathname tree = Some subtree ->
    find_subtree (pathname ++ suffix) (update_subtree pathname subtree' tree) = Some r ->
    find_subtree suffix subtree' = Some r.
Proof.
(* original proof tokens: 105 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_head_name' : forall  rest name  f,
    map fst (map (update_subtree_helper f name) rest) = map fst rest.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Theorem find_update_subtree : forall fnlist tree subtree subtree0,
    find_subtree fnlist tree = Some subtree0 ->
    find_subtree fnlist (update_subtree fnlist subtree tree) = Some subtree.
Proof.
(* original proof tokens: 98 *)

(* No more tactics to try *)
Admitted.

Hint Resolve find_update_subtree.
Lemma find_update_subtree_suffix: forall path suffix tree subtree d,
    find_subtree path tree = Some d ->
    find_subtree (path++suffix) (update_subtree path subtree tree) =
    find_subtree suffix subtree.
Proof.
(* original proof tokens: 97 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_update_subtree_ne_file :
    forall p2 p1 tree inum1 inum2 f1 f1' f2,
    find_subtree p1 tree = Some (TreeFile inum1 f1) ->
    find_subtree p2 tree = Some (TreeFile inum2 f2) ->
    p1 <> p2 ->
    find_subtree p2 (update_subtree p1 (TreeFile inum1 f1') tree) =
    find_subtree p2 tree.
Proof.
(* original proof tokens: 303 *)

(* No more tactics to try *)
Admitted.

Lemma tree_graft_not_in_dirents : forall path ents name tree subtree dnum,
    ~ In name (map fst ents) ->
    update_subtree path (TreeDir dnum (ents ++ [(name, subtree)])) tree =
    tree_graft dnum ents path name subtree tree.
Proof.
(* original proof tokens: 96 *)

(* No more tactics to try *)
Admitted.

Lemma find_dirlist_same: forall ents name b subtree,
    NoDup (name :: (map fst ents)) ->
    find_dirlist name ((name, b) :: ents) = Some subtree ->
    b = subtree.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma find_dirlist_ne: forall name1 name2 b ents,
    NoDup (name2 :: (map fst ents)) ->
    name1 <> name2 ->
    find_dirlist name1 ((name2, b) :: ents) = find_dirlist name1 ents .
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma find_dirlist_in : forall name ents tree,
     find_dirlist name ents = Some tree ->
     In name (map fst ents).
Proof.
(* original proof tokens: 68 *)

(* No more tactics to try *)
Admitted.

Lemma find_dirlist_find_subtree_helper : forall ents tree name,
    find_dirlist name ents = Some tree ->
    NoDup (map fst ents) ->
    fold_right (find_subtree_helper (fun x => Some x) name) None ents = Some tree.
Proof.
(* original proof tokens: 102 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_helper_in : forall T (rec : _ -> option T) ents name node,
    fold_right (find_subtree_helper rec name) None ents = Some node ->
    In name (map fst ents).
Proof.
(* original proof tokens: 68 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_delete' : forall pathname name ents inum dnum f,
    NoDup (map fst ents) ->
    find_subtree pathname (TreeDir dnum (delete_from_list name ents)) = Some (TreeFile inum f) ->
    find_subtree pathname (TreeDir dnum ents) = Some (TreeFile inum f).
Proof.
(* original proof tokens: 135 *)

(* No more tactics to try *)
Admitted.

Lemma find_name_exists : forall path tree inum isdir,
    find_name path tree = Some (inum, isdir)
    -> exists subtree, find_subtree path tree = Some subtree
        /\ dirtree_inum subtree = inum /\ dirtree_isdir subtree = isdir.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma tree_prune_preserve_inum : forall path name tree inum ents,
    find_subtree path tree = Some (TreeDir inum ents)
    -> dirtree_inum (tree_prune inum ents path name tree) = dirtree_inum tree.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma tree_prune_preserve_isdir : forall path name tree inum ents,
    find_subtree path tree = Some (TreeDir inum ents)
    -> dirtree_isdir (tree_prune inum ents path name tree) = dirtree_isdir tree.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma tree_graft_preserve_inum : forall path name tree subtree inum ents,
    find_subtree path tree = Some (TreeDir inum ents)
    -> dirtree_inum (tree_graft inum ents path name subtree tree) = dirtree_inum tree.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma tree_graft_preserve_isdir : forall path name tree subtree inum ents,
    find_subtree path tree = Some (TreeDir inum ents)
    -> dirtree_isdir (tree_graft inum ents path name subtree tree) = dirtree_isdir tree.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_dirlist : forall name inum ents,
    find_subtree (name :: nil) (TreeDir inum ents) = find_dirlist name ents.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma update_subtree_preserve_name : forall l fnlist s subtree,
    map fst (map (update_subtree_helper (update_subtree fnlist subtree) s) l) = map fst l.
Proof.
(* original proof tokens: 58 *)

(* No more tactics to try *)
Admitted.

Lemma update_dirtree_preserve_name: forall l name newtree,
    map fst (map (update_subtree_helper (fun _: dirtree => newtree) name) l) = map fst l.
Proof.
(* original proof tokens: 79 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_leaf_in : forall ents name tree dnum,
    In (name, tree) ents ->
    NoDup (map fst ents) ->
    find_subtree [ name ] (TreeDir dnum ents) = Some tree.
Proof.
(* original proof tokens: 97 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_app': forall suffix path tree subtree,
    find_subtree (path++suffix) tree = Some subtree ->
    exists subtree_base, find_subtree path tree = Some subtree_base /\
      find_subtree suffix subtree_base = Some subtree.
Proof.
(* original proof tokens: 112 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_head: forall l name n d,
    find_subtree [name] (TreeDir n ((name,d) :: l)) = Some d.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_head_ne: forall name s n d l,
    name <> s ->
    find_subtree [name] (TreeDir n ((s,d) :: l)) = find_subtree [name] (TreeDir n l).
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_head_pn: forall pn s n d l,
    pathname_prefix [s] pn ->
    find_subtree pn (TreeDir n ((s, d) :: l)) =
    find_subtree pn (TreeDir n [(s, d)]).
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_head_ne_pn: forall pn s n d l,
    pn <> [] ->
    ~pathname_prefix [s] pn ->
    find_subtree pn (TreeDir n ((s, d) :: l)) =
    find_subtree pn (TreeDir n l).
Proof.
(* original proof tokens: 86 *)

(* No more tactics to try *)
Admitted.

Lemma update_subtree_update_trim_head_dir: forall l name path n subtree_head subtree,
    find_subtree [name] (TreeDir n l) = Some subtree_head ->
    find_subtree [name] (update_subtree ([name]++path) subtree (TreeDir n l)) =
      Some (update_subtree path subtree subtree_head).
Proof.
(* original proof tokens: 175 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_update_trim_head: forall name path subtree tree subtree_head,
    find_subtree [name] tree = Some subtree_head ->
    find_subtree [name] (update_subtree ([name] ++ path) subtree tree) =
      Some (update_subtree path subtree subtree_head).
Proof.
(* original proof tokens: 60 *)

(* No more tactics to try *)
Admitted.

Lemma update_subtree_update_trim_head_ne: forall tree name s path subtree,
    s <> name ->
    find_subtree [name] (update_subtree (s::path) subtree tree) = 
        find_subtree [name] tree.
Proof.
(* original proof tokens: 115 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_update_subtree_child: forall path suffix tree subtree subtree_child, 
      find_subtree path tree = Some subtree_child ->
      find_subtree path (update_subtree (path++suffix) subtree tree) = 
       Some (update_subtree suffix subtree subtree_child).
Proof.
(* original proof tokens: 108 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_update_trim: forall p1 p2 a tree elem subtree d,
    find_subtree [a] tree = Some subtree ->
    find_subtree p2 subtree = Some d ->
    find_subtree p1 (update_subtree p2 elem subtree) = find_subtree p1 subtree ->
    find_subtree (a :: p1) (update_subtree (a::p2) elem tree) = find_subtree (a :: p1) tree.
Proof.
(* original proof tokens: 113 *)

(* No more tactics to try *)
Admitted.

Theorem find_subtree_update_subtree_oob'' : forall pn tree a subtree,
    pn <> nil ->
    (~ pathname_prefix [a] pn) ->
    find_subtree [a] (update_subtree pn subtree tree) = find_subtree [a] tree.
Proof.
(* original proof tokens: 70 *)

(* No more tactics to try *)
Admitted.

Theorem find_subtree_update_subtree_none : forall tree a suffix subtree,
    find_subtree [a] tree = None ->
    find_subtree [a] (update_subtree ([a]++suffix) subtree tree) = None.
Proof.
(* original proof tokens: 180 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_none_In: forall name n l,
    find_subtree [name] (TreeDir n l) = None ->
    ~In name (map fst l).
Proof.
(* original proof tokens: 94 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_delete_same' : forall l rest name n,
    NoDup (map fst l) ->
    find_subtree (name :: rest) (TreeDir n (delete_from_list name l)) = None.
Proof.
(* original proof tokens: 74 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_delete_same : forall l rest name n,
    NoDup (map fst l) ->
    find_subtree (name :: rest) (delete_from_dir name (TreeDir n l)) = None.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_delete_ne' : forall l suffix name name' n,
    NoDup (map fst l) ->
    name <> name' ->
    find_subtree (name :: suffix) (TreeDir n (delete_from_list name' l)) = 
      find_subtree (name :: suffix) (TreeDir n l).
Proof.
(* original proof tokens: 136 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_delete_ne : forall l suffix name name' n,
    NoDup (map fst l) ->
    name <> name' ->
    find_subtree (name :: suffix) (delete_from_dir name' (TreeDir n l)) = 
      find_subtree (name :: suffix) (TreeDir n l).
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma In_delete_from_list_snd : forall l x name,
    In x (map snd (delete_from_list name l)) ->
    In x (map snd l).
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma In_delete_from_list_fst : forall l x name,
    In x (map fst (delete_from_list name l)) ->
    In x (map fst l).
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma NoDup_delete_from_list : forall l name,
    NoDup (map fst l) ->
    NoDup (map fst (delete_from_list name l)).
Proof.
(* original proof tokens: 73 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_add_to_dir_same: forall name suffix n subtree l,
    find_subtree (name :: suffix) (TreeDir n (add_to_list name subtree l)) =
    find_subtree suffix subtree.
Proof.
(* original proof tokens: 147 *)

(* No more tactics to try *)
Admitted.

Lemma lookup_name: forall tree_elem name subtree dnum tree,
    find_subtree [name] (update_subtree [] (add_to_dir name subtree (TreeDir dnum tree_elem)) tree) = Some subtree.
Proof.
(* original proof tokens: 107 *)

(* No more tactics to try *)
Admitted.

Lemma lookup_firstelem_path: forall  suffix tree a f,
    find_subtree (a::suffix) tree = Some f ->
    exists d, find_subtree [a] tree = Some d /\ find_subtree suffix d = Some f.
Proof.
(* original proof tokens: 73 *)

(* No more tactics to try *)
Admitted.

Lemma lookup_firstelem_path_r: forall a dir name suffix subtree tree childdir,
    find_subtree [a] tree = Some childdir /\ 
        find_subtree (suffix ++ [name]) (update_subtree suffix (add_to_dir name subtree dir) childdir) = Some subtree ->
    find_subtree ((a::suffix) ++ [name]) (update_subtree (a::suffix) (add_to_dir name subtree dir) tree) = Some subtree.
Proof.
(* original proof tokens: 135 *)

(* No more tactics to try *)
Admitted.

Lemma lookup_path: forall prefix name subtree dir tree dnum tree_elem,
    dir = (TreeDir dnum tree_elem) ->
    find_subtree prefix tree = Some dir ->
    find_subtree (prefix ++ [name]) (update_subtree prefix (add_to_dir name subtree dir) tree)
        = Some subtree.
Proof.
(* original proof tokens: 86 *)

(* No more tactics to try *)
Admitted.

Theorem find_subtree_tree_graft: forall prefix name tree dnum tree_elem subtree,
    find_subtree prefix tree = Some (TreeDir dnum tree_elem) ->
    find_subtree (prefix++[name]) (tree_graft dnum tree_elem prefix name subtree tree) = Some subtree.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Lemma update_update_subtree_same : forall pn tree subtree subtree',
    update_subtree pn subtree (update_subtree pn subtree' tree) = update_subtree pn subtree tree.
Proof.
(* original proof tokens: 87 *)

(* No more tactics to try *)
Admitted.

Theorem dirtree_dir_parts : forall t,
    dirtree_isdir t = true ->
    t = TreeDir (dirtree_inum t) (dirtree_dirents t).
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Theorem dirtree_file_parts : forall t,
    dirtree_isdir t = false ->
    t = TreeFile (dirtree_inum t) (dirtree_file t).
Proof.
(* original proof tokens: 19 *)
(* generated proof tokens: 134 *)
simpl. destruct t; auto.
unfold dirtree_isdir in *.
destruct (TreeDir n l); intros; subst; auto.
rewrite dirtree_dir_parts.
destruct (dirtree_isdir (TreeFile (dirtree_inum (TreeDir n0 l0)) (dirtree_file (TreeDir n0 l0))));
  try discriminate.
unfold dirtree_isdir in *.
destruct (TreeFile (dirtree_inum (TreeDir n0 l0)) (dirtree_file (TreeDir n0 l0))).
discriminate.
discriminate H.
Qed.

Lemma find_subtree_file_none: forall s suffix n b,
    find_subtree (s::suffix) (TreeFile n b) = None.
Proof.
(* original proof tokens: 26 *)
(* generated proof tokens: 198 *)

intros s suffix n b.
induction suffix as [|h t IH].
- (* Case for empty suffix *)
  simpl. (* find_subtree (s :: nil) (TreeFile n b) = None *)
  reflexivity.
- (* Case for non-empty suffix *)
  simpl. (* find_subtree (s :: (h :: t)) (TreeFile n b) *)
  destruct (string_dec s h) as [Heq | Hneq].
  + (* If s = h, then we cannot continue to search in a file *)
    subst h. (* s is now equal to h *)
    simpl. (* We have a TreeFile *)
    reflexivity.
  + (* If s <> h, it can return None *)
    simpl in IH. (* find_subtree (h::t) (TreeFile n b) = None implies continuing search is pointless *)
    apply IH. (* Proceeding with the induction hypothesis *)
Qed.

Lemma find_subtree_file_dir_exfalso: forall pn n f d e,
    find_subtree pn (TreeFile n f) = Some (TreeDir d e) ->
    False.
Proof.
(* original proof tokens: 40 *)
intros pn n f d e H.
  destruct H.
(* No more tactics to try *)
Admitted.

Theorem find_subtree_graft_subtree_oob: forall pn num ents base name tree subtree inum f,
    find_subtree base tree = Some (TreeDir num ents) ->
    (~ pathname_prefix (base ++ [name]) pn) ->
    find_subtree pn tree = Some (TreeFile inum f) ->
    find_subtree pn (tree_graft num ents base name subtree tree) = Some (TreeFile inum f).
Proof.
(* original proof tokens: 246 *)

(* No more tactics to try *)
Admitted.

Theorem find_subtree_graft_subtree_oob': forall pn num ents base name tree subtree inum f,
    find_subtree base tree = Some (TreeDir num ents) ->
    (~ pathname_prefix (base ++ [name]) pn) ->
    find_subtree pn (tree_graft num ents base name subtree tree) = Some (TreeFile inum f) ->
    find_subtree pn tree = Some (TreeFile inum f).
Proof.
(* original proof tokens: 311 *)

(* No more tactics to try *)
Admitted.

Theorem find_subtree_prune_subtree_oob: forall pn num ents base name tree inum f,
    find_subtree base tree = Some (TreeDir num ents) ->
    (~ pathname_prefix (base ++ [name]) pn) ->
    find_subtree pn tree = Some (TreeFile inum f) ->
    find_subtree pn (tree_prune num ents base name tree) = Some (TreeFile inum f).
Proof.
(* original proof tokens: 246 *)

(* No more tactics to try *)
Admitted.

Theorem find_subtree_prune_subtree_oob': forall pn num ents base name tree inum f,
    find_subtree base tree = Some (TreeDir num ents) ->
    (~ pathname_prefix (base ++ [name]) pn) ->
    find_subtree pn (tree_prune num ents base name tree) = Some (TreeFile inum f) ->
    find_subtree pn tree = Some (TreeFile inum f).
Proof.
(* original proof tokens: 249 *)

(* No more tactics to try *)
Admitted.

Lemma find_rename_oob: forall tree subtree cwd dnum tree_elem srcnum srcbase 
         srcents srcname dstnum dstbase dstents dstname pathname inum f,
    (~ pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname) ->
    (~ pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname) -> 
    find_subtree pathname tree = Some (TreeFile inum f) ->
    find_subtree cwd tree = Some (TreeDir dnum tree_elem) ->
    find_subtree srcbase (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some subtree ->
    find_subtree dstbase
      (tree_prune srcnum srcents srcbase srcname (TreeDir dnum tree_elem)) =
      Some (TreeDir dstnum dstents) ->
    find_subtree pathname
     (update_subtree cwd
       (tree_graft dstnum dstents dstbase dstname subtree
        (tree_prune srcnum srcents srcbase srcname (TreeDir dnum tree_elem)))
     tree) = Some (TreeFile inum f).
Proof.
(* original proof tokens: 252 *)

(* No more tactics to try *)
Admitted.

Lemma find_rename_oob': forall tree subtree cwd dnum tree_elem srcnum srcbase 
         srcents srcname dstnum dstbase dstents dstname pathname inum f,
    (~ pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname) ->
    (~ pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname) -> 
    find_subtree cwd tree = Some (TreeDir dnum tree_elem) ->
    find_subtree srcbase (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some subtree ->
    find_subtree dstbase
      (tree_prune srcnum srcents srcbase srcname (TreeDir dnum tree_elem)) =
      Some (TreeDir dstnum dstents) ->
    find_subtree pathname
     (update_subtree cwd
       (tree_graft dstnum dstents dstbase dstname subtree
        (tree_prune srcnum srcents srcbase srcname (TreeDir dnum tree_elem)))
     tree) = Some (TreeFile inum f) ->
    find_subtree pathname tree = Some (TreeFile inum f).
Proof.
(* original proof tokens: 275 *)

(* No more tactics to try *)
Admitted.

Lemma dirtree_name_in_dents: forall T name tree_elem elem f,
    fold_right (find_subtree_helper f name) (@None T) tree_elem = Some elem
    -> In name (map fst tree_elem).
Proof.
(* original proof tokens: 127 *)

(* No more tactics to try *)
Admitted.

