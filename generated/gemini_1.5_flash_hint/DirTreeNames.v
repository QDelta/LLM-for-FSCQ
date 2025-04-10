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
(* hint proof tokens: 146 *)
Proof.
    induction tree using dirtree_ind2; simpl; intros.
    - constructor.
    - constructor.
      2: rewrite dir_names_distinct in H0; destruct_lift H0; eauto.

      apply Forall_forall. intros.
      rewrite Forall_forall in H.
      specialize (H x H1).

      apply in_map_iff in H1; repeat deex.
      destruct x0; simpl in *.
      apply in_split in H3; repeat deex.

      rewrite dirlist_pred_split in H0. simpl in H0.
      eapply H with (xp := xp).
      pred_apply' H0.
      cancel.
  Qed.
Lemma rep_tree_names_distinct : forall tree F fsxp Ftop m ilist frees ms sm,
    (F * rep fsxp Ftop tree ilist frees ms sm)%pred m ->
    tree_names_distinct tree.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_update_subtree : forall pn t subtree,
    tree_names_distinct t ->
    tree_names_distinct subtree ->
    tree_names_distinct (update_subtree pn subtree t).
(* hint proof tokens: 191 *)
Proof.
    induction pn; simpl; eauto; intros.
    destruct t; eauto.
    constructor.
    - induction l; simpl; constructor.
      + destruct a0; simpl.
        inversion H; simpl in *; subst.
        inversion H3; subst.
        destruct (string_dec s a); subst; simpl; eauto.
      + eapply IHl.
        inversion H; subst.
        inversion H3; subst.
        inversion H4; subst.
        constructor; eauto.
    - inversion H; subst.
      replace (map fst (map (update_subtree_helper (update_subtree pn subtree) a) l)) with (map fst l); eauto.
      clear H H3 H4.
      induction l; simpl; eauto.
      f_equal; eauto.
      destruct a0; simpl.
      destruct (string_dec s a); eauto.
  Qed.
Theorem tree_names_distinct_head : forall n a d l,
    tree_names_distinct (TreeDir n ((a, d) :: l)) ->
    tree_names_distinct (TreeDir n ([(a, d)])).
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

Theorem tree_names_distinct_child : forall n a d l,
    tree_names_distinct (TreeDir n ((a, d) :: l)) ->
    tree_names_distinct d.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Hint Resolve tree_names_distinct_child.
Lemma tree_names_distinct_next : forall n s d l,
    tree_names_distinct (TreeDir n ((s, d) :: l)) ->
    tree_names_distinct (TreeDir n l).
(* hint proof tokens: 33 *)
Proof.
    intros.
    inversion H.
    constructor.
    inversion H2; eauto.
    inversion H3; eauto.
  Qed.
Hint Resolve tree_names_distinct_next.
Lemma tree_names_distinct_head_not_rest : forall inum e ents name path subtree,
    tree_names_distinct (TreeDir inum (e :: ents)) ->
    find_subtree (name::path) (TreeDir inum ents) = Some subtree ->
    find_subtree (name::path) (TreeDir inum (e :: ents)) = Some subtree.
(* hint proof tokens: 103 *)
Proof.
    destruct e; simpl; intros.
    destruct (string_dec s name); eauto; subst.
    inversion H.
    inversion H4; subst.
    clear H H3 H4 H8.
    exfalso.
    induction ents; simpl in *; try congruence.
    destruct a; simpl in *; intuition.
    destruct (string_dec s name); simpl in *; try congruence.
    eapply IHents; eauto.
  Qed.
Lemma tree_names_distinct_head_name : forall inum name subtree rest,
    tree_names_distinct (TreeDir inum ((name, subtree) :: rest)) ->
    ~ In name (map fst rest).
Proof.
(* original proof tokens: 24 *)
intros. inversion H; subst.
apply NoDup_app_not_In; auto.
apply NoDup_app_comm.
(* No more tactics to try *)
Admitted.

Lemma tree_name_distinct_rest: forall inum x l,
        tree_names_distinct (TreeDir inum (x::l)) ->
        tree_names_distinct (TreeDir inum l).
Proof.
(* original proof tokens: 60 *)

(* No more tactics to try *)
Admitted.

Lemma tree_name_distinct_head: forall inum name l t,
        tree_names_distinct (TreeDir inum ((name, t)::l)) ->
        tree_names_distinct t.
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_subtree : forall path tree subtree,
    tree_names_distinct tree ->
    find_subtree path tree = Some subtree ->
    tree_names_distinct subtree.
(* hint proof tokens: 125 *)
Proof.
    induction path.
    intros; inversion H0; subst; auto.
    induction tree; simpl; try congruence; intros.
    inversion H0; subst.

    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst; simpl in *.
    - inversion H; inversion H4; subst; simpl in *.
      eapply IHpath; eauto.
    - inversion H; inversion H4; subst; simpl in *.
      apply IHl; eauto.
  Qed.
Lemma tree_names_distinct_nodup : forall dnum ents,
    tree_names_distinct (TreeDir dnum ents) ->
    NoDup (map fst ents).
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_delete_from_list : forall l n name,
    tree_names_distinct (TreeDir n l) ->
    tree_names_distinct (TreeDir n (delete_from_list name l)).
Proof.
(* original proof tokens: 132 *)
intros. inversion H; subst. constructor.
induction l; simpl; auto; intros.
inversion H; subst; eauto.
(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_delete_ne: forall l path name' n subtree,
    NoDup (map fst l) ->
    (~ pathname_prefix [name'] path) ->
    tree_names_distinct (TreeDir n l) ->
    find_subtree path (delete_from_dir name' (TreeDir n l)) = Some subtree ->
    tree_names_distinct subtree.
(* hint proof tokens: 92 *)
Proof.
    induction path; intros; auto.
    - unfold find_subtree in H2; subst; simpl. 
      inversion H2.
      eapply tree_names_distinct_delete_from_list; eauto.
    - rewrite find_subtree_delete_ne in H2; eauto.
      eapply tree_names_distinct_subtree; eauto.
      intro.
      eapply pathname_prefix_head_neq'; eauto.
  Qed.
Lemma tree_names_distinct_prune_child_subtree: forall path suffix tree name subtree n l,
    tree_names_distinct tree ->
    find_subtree (path ++ suffix) tree = Some (TreeDir n l) ->
    find_subtree path (update_subtree (path++suffix) (delete_from_dir name (TreeDir n l)) tree) 
      = Some subtree ->
    tree_names_distinct subtree.
(* hint proof tokens: 105 *)
Proof.
    intros.
    eapply find_subtree_app' in H0 as H0'.
    destruct H0'; intuition.
    erewrite find_subtree_update_subtree_child in H1; eauto.
    inversion H1.
    eapply tree_names_distinct_update_subtree.
    eapply tree_names_distinct_subtree; eauto.
    eapply tree_names_distinct_delete_from_list; eauto.
    eapply tree_names_distinct_subtree; eauto.
  Qed.
Lemma update_subtree_path_notfound: forall p tree subtree,
    tree_names_distinct tree ->
    find_subtree p tree = None ->
    update_subtree p subtree tree = tree.
(* hint proof tokens: 221 *)
Proof.
    induction p; intros; subst.
    - simpl in *. exfalso. inversion H0.
    - destruct tree; simpl; eauto.
      f_equal.
      induction l; subst; simpl; eauto.
      destruct a0.
      destruct (string_dec a s); subst.
      simpl.
      destruct (string_dec s s); try congruence.
      rewrite update_subtree_notfound; eauto.
      erewrite IHp; eauto.
      simpl in H0.
      destruct (string_dec s s) in H0; try congruence.
      eapply tree_names_distinct_nodup in H.
      simpl in H.
      inversion H; eauto.
      simpl.
      destruct (string_dec s a); try congruence.
      f_equal.
      eapply IHl.
      eapply tree_name_distinct_rest in H; eauto.
      simpl in H0.
      destruct (string_dec s a) in H0; try congruence.
      simpl; eauto.
  Qed.
Lemma find_subtree_update_subtree_ne_path : forall p1 p2 tree subtree,
    tree_names_distinct tree ->
    (~ pathname_prefix p2 p1) ->
    (~ pathname_prefix p1 p2) ->
    find_subtree p1 (update_subtree p2 subtree tree) = find_subtree p1 tree.
Proof.
(* original proof tokens: 540 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_prune_subtree : forall path tree path' name subtree n l,
    tree_names_distinct tree ->
    find_subtree path' tree = Some (TreeDir n l) ->
    find_subtree path (tree_prune n l path' name tree) = Some subtree ->
    tree_names_distinct subtree.
(* hint proof tokens: 356 *)
Proof.
    intros.
    unfold tree_prune in *.
    destruct (pathname_decide_prefix path' path).
    + 
      
      destruct (list_eq_dec string_dec path' path); subst.
      - erewrite find_update_subtree in H1; eauto.
        inversion H1; subst.
        eapply tree_names_distinct_delete_from_list; eauto.
        eapply tree_names_distinct_subtree; eauto.
      -          
        destruct H2; subst.
        erewrite find_subtree_app in H1; eauto.
        destruct (pathname_decide_prefix [name] x).
        destruct H2; subst.
        -- 
          erewrite find_subtree_app_none in H1.
          exfalso; congruence.
          erewrite find_subtree_delete_same; eauto.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
         -- 
          eapply tree_names_distinct_delete_ne; eauto.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
          eapply pathname_prefix_neq; eauto.
          eapply tree_names_distinct_subtree; eauto.
    + destruct (pathname_decide_prefix path path').
      - 
        destruct H3; subst.
        eapply tree_names_distinct_prune_child_subtree; eauto.
      - 
        erewrite find_subtree_update_subtree_ne_path in H1; eauto.
        eapply tree_names_distinct_subtree; eauto.
        eapply pathname_prefix_neq; eauto.
        eapply pathname_prefix_neq; eauto.
  Qed.
Lemma tree_names_distinct_prune_subtree' : forall inum ents base name tree,
    tree_names_distinct tree ->
    find_subtree base tree = Some (TreeDir inum ents) ->
    tree_names_distinct (tree_prune inum ents base name tree).
(* hint proof tokens: 45 *)
Proof.
    intros.
    eapply tree_names_distinct_prune_subtree with (path := nil) in H0.
    eauto.
    eauto.
    simpl; eauto.
  Qed.
Lemma find_subtree_add_to_list_oob: forall ents dnum s name subtree d,
    tree_names_distinct (TreeDir dnum ents) ->
    s <> name ->
    find_subtree [s] (TreeDir dnum (add_to_list name subtree ents)) = Some d ->
    find_subtree [s] (TreeDir dnum ents) = Some d.
Proof.
(* original proof tokens: 181 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_add_to_dir_oob: forall suffix name dnum ents subtree inum f,
     tree_names_distinct (TreeDir dnum ents) ->
     (~pathname_prefix [name] suffix) ->
     find_subtree suffix (add_to_dir name subtree (TreeDir dnum ents)) = Some (TreeFile inum f)->
     find_subtree suffix (add_to_dir name subtree (TreeDir dnum ents)) = find_subtree suffix (TreeDir dnum ents).
Proof.
(* original proof tokens: 147 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_add_to_dir_oob': forall suffix name tree subtree inum f,
     tree_names_distinct tree ->
     (~pathname_prefix [name] suffix) ->
     find_subtree suffix (add_to_dir name subtree tree) = Some (TreeFile inum f)->
     find_subtree suffix (add_to_dir name subtree tree) = find_subtree suffix tree.
(* hint proof tokens: 65 *)
Proof.
    intros. destruct tree.
    - simpl in H1. 
      destruct suffix.
      + simpl; eauto.
      + unfold find_subtree in H1; simpl.
        inversion H1.
    - erewrite find_subtree_add_to_dir_oob; eauto.
  Qed.
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
(* original proof tokens: 1922 *)

(* No more tactics to try *)
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
(* hint proof tokens: 317 *)
Proof.
    intros; cbn.
    destruct (pathname_decide_prefix srcpath pathname).
    -- 
      deex. 
      denote update_subtree as Hx.
      erewrite find_update_subtree_suffix in Hx; eauto.
      {
        destruct suffix.
        - rewrite app_nil_r in *. unfold find_subtree in Hx; inversion Hx.
        - destruct (string_dec srcname s); subst.
          + exfalso. eapply H. exists suffix. rewrite <- app_assoc.
            f_equal.
          + erewrite find_subtree_delete_ne' in Hx.
            erewrite find_subtree_app; eauto.
            eapply tree_names_distinct_nodup; eauto.
            eapply tree_names_distinct_subtree; eauto.
            congruence.
      }
    -- destruct (pathname_decide_prefix pathname srcpath).
      {
        deex.
        eapply find_subtree_app' in H3. deex; intuition.
        destruct subtree_base; try congruence.
        + unfold find_subtree in H7.
          destruct suffix; try congruence.
        + erewrite find_subtree_update_subtree_child in H4; eauto.
          destruct suffix; unfold update_subtree in H4; try congruence.
       }
      
      erewrite find_subtree_update_subtree_ne_path in H4; eauto.
      eapply pathname_prefix_neq; eauto.
      eapply pathname_prefix_neq; eauto.
  Qed.
Theorem update_subtree_app : forall p0 p1 tree subtree t,
    tree_names_distinct tree ->
    find_subtree p0 tree = Some subtree ->
    update_subtree (p0 ++ p1) t tree = update_subtree p0 (update_subtree p1 t subtree) tree.
(* hint proof tokens: 134 *)
Proof.
    induction p0; simpl; intros.
    congruence.
    destruct tree; try congruence.
    f_equal.
    induction l; simpl in *; intros; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst; eauto.
    - erewrite IHp0; eauto.
      f_equal.
      repeat rewrite update_subtree_notfound; eauto.
      inversion H; inversion H4; eauto.
      inversion H; inversion H4; eauto.
    - f_equal.
      eapply IHl; eauto.
  Qed.
Lemma find_subtree_dir_after_update_subtree : forall base pn t num ents subtree,
    tree_names_distinct t ->
    find_subtree pn t = Some (TreeDir num ents) ->
    ~ (exists suffix : list string, pn = base ++ suffix) ->
    exists ents,
    find_subtree pn (update_subtree base subtree t) = Some (TreeDir num ents).
Proof.
(* original proof tokens: 200 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_none_after_update_subtree : forall base pn t subtree,
    tree_names_distinct t ->
    find_subtree pn t = None ->
    ~ (exists suffix : list string, pn = base ++ suffix) ->
    find_subtree pn (update_subtree base subtree t) = None.
Proof.
(* original proof tokens: 190 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_tree_names_distinct: forall pn t subtree,
      tree_names_distinct t ->
      find_subtree pn t = Some subtree ->
      tree_names_distinct subtree.
(* hint proof tokens: 109 *)
Proof.
    induction pn; intros; simpl in *.
    - congruence.
    - destruct t; try congruence.
      induction l.
      -- simpl in *; try congruence.
      -- destruct a0; subst; simpl in *.
        destruct (string_dec s a); subst; simpl in *.
        + eapply IHpn. 2: eauto.
          eapply tree_names_distinct_child; eauto.
        + eapply IHl; eauto.
  Qed.
Lemma find_subtree_before_prune_general : forall pn t num ents base name subtree,
    tree_names_distinct t ->
    find_subtree base t = Some (TreeDir num ents) ->
    find_subtree pn (tree_prune num ents base name t) = Some subtree ->
    exists subtree',
      find_subtree pn t = Some subtree' /\
      dirtree_inum subtree = dirtree_inum subtree' /\
      dirtree_isdir subtree = dirtree_isdir subtree'.
Proof.
(* original proof tokens: 547 *)
unfold tree_prune; intros.
(* No more tactics to try *)
Admitted.

Lemma find_subtree_before_prune : forall pn t num ents base name dnum0 ents0,
    tree_names_distinct t ->
    find_subtree base t = Some (TreeDir num ents) ->
    find_subtree pn (tree_prune num ents base name t) = Some (TreeDir dnum0 ents0) ->
    exists ents1,
    find_subtree pn t = Some (TreeDir dnum0 ents1).
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Lemma find_subtree_pruned_none : forall tree base name basenum basedents,
    tree_names_distinct tree ->
    find_subtree base tree = Some (TreeDir basenum basedents) ->
    find_subtree (base ++ [name]) (tree_prune basenum basedents base name tree) = None.
(* hint proof tokens: 154 *)
Proof.
    intros.
    unfold tree_prune.
    erewrite find_subtree_app.
    2: erewrite find_update_subtree; eauto.
    simpl.
    eapply find_subtree_tree_names_distinct in H0; eauto.
    inversion H0; clear H0; subst.
    clear H3.
    induction basedents; simpl in *; eauto.
    destruct a.
    destruct (string_dec s name); subst.
    - rewrite find_subtree_ents_not_in; eauto.
      inversion H4; eauto.
    - simpl.
      destruct (string_dec s name); try congruence.
      eapply IHbasedents.
      inversion H4; eauto.
  Qed.
Lemma update_name_twice: forall tree_elem name tree subtree subtree' dnum,
    tree_names_distinct
      (update_subtree ([name]) subtree'
         (update_subtree [] (add_to_dir name subtree (TreeDir dnum tree_elem))
            tree)) ->
    update_subtree [name] subtree' (update_subtree [] (add_to_dir name subtree (TreeDir dnum tree_elem)) tree) =
    update_subtree [] (add_to_dir name subtree' (TreeDir dnum tree_elem)) tree.
Proof.
(* original proof tokens: 181 *)

(* No more tactics to try *)
Admitted.

Lemma update_update_subtree_twice: forall prefix name subtree' subtree d dnum tree_elem,
    tree_names_distinct 
       (update_subtree (prefix ++ [name]) subtree'
          (update_subtree prefix
             (add_to_dir name subtree (TreeDir dnum tree_elem)) d)) ->
    update_subtree (prefix ++ [name]) subtree'
       (update_subtree prefix (add_to_dir name subtree (TreeDir dnum tree_elem)) d) =
        update_subtree prefix (add_to_dir name subtree' (TreeDir dnum tree_elem)) d.
(* hint proof tokens: 217 *)
Proof.
   induction prefix; intros.
   - rewrite app_nil_l.
     rewrite update_name_twice by auto.
     reflexivity.
   - destruct d. 
     simpl.
     reflexivity.
     induction l; subst; simpl.
     + reflexivity.
     + destruct a0.
      simpl in *.
      destruct (string_dec s a).
      simpl in *.
      destruct (string_dec s a).
      subst; simpl in *.
      erewrite IHprefix.
      apply tree_name_distinct_rest in H.
      specialize (IHl H).
      inversion IHl.
      rewrite H1.
      eauto.
      eapply tree_name_distinct_head.
      eauto.
      exfalso.
      congruence.
      simpl in *.
      destruct (string_dec s a).
      exfalso.
      congruence.
      simpl in *.
      apply tree_name_distinct_rest in H.
      specialize (IHl H).
      inversion IHl.
      rewrite H1.
      eauto.
  Qed.
Theorem update_subtree_tree_graft: 
    forall prefix name tree dnum tree_elem subtree subtree' F Ftop m fsxp ilist frees ms sm,
    (F * rep fsxp Ftop (update_subtree (prefix++[name]) subtree' 
                        (tree_graft dnum tree_elem prefix name subtree tree)) ilist frees ms sm)%pred m -> 
    find_subtree prefix tree = Some (TreeDir dnum tree_elem) ->
    update_subtree (prefix++[name]) subtree' (tree_graft dnum tree_elem prefix name subtree tree) = 
            (tree_graft dnum tree_elem prefix name subtree' tree).
(* hint proof tokens: 59 *)
Proof.
    intros.
    unfold tree_graft in *.
    erewrite update_update_subtree_twice with (dnum := dnum) (tree_elem := tree_elem).
    reflexivity.
    eapply rep_tree_names_distinct.
    eauto.
  Qed.
