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
(* hint proof tokens: 30 *)
Proof.
    unfold tree_inodes_distinct; simpl; intros.
    rewrite cons_app in *.
    eauto.
  Qed.
Theorem tree_inodes_distinct_head : forall n a d l,
    tree_inodes_distinct (TreeDir n ((a, d) :: l)) ->
    tree_inodes_distinct (TreeDir n ([(a,d)])).
Proof.
(* skipped proof tokens: 52 *)
Admitted.
Theorem dirtree_update_inode_absent : forall tree inum off v,
    ~ In inum (tree_inodes tree) ->
    dirtree_update_inode tree inum off v = tree.
(* hint proof tokens: 86 *)
Proof.
    induction tree using dirtree_ind2; simpl in *; intros; intuition.
    - destruct (addr_eq_dec inum0 inum); congruence.
    - f_equal.
      induction tree_ents; simpl; auto.
      destruct a; simpl in *.
      inversion H.
      rewrite H4 by eauto.
      rewrite IHtree_ents; eauto.
  Qed.
Theorem find_subtree_inum_present : forall pathname tree sub,
    find_subtree pathname tree = Some sub ->
    In (dirtree_inum sub) (tree_inodes tree).
(* hint proof tokens: 85 *)
Proof.
    induction pathname; simpl; intros.
    - inversion H; subst.
      destruct sub; simpl; eauto.
    - destruct tree; try congruence.
      induction l; simpl in *; try congruence.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst; eauto.
      edestruct IHl; eauto.
  Qed.
Hint Resolve tree_inodes_distinct_child.
Hint Resolve find_subtree_inum_present.
Lemma dirtree_update_inode_absent' : forall l inum off v,
    ~ In inum (concat (map (fun e => tree_inodes (snd e)) l)) ->
    dirlist_update (fun t' : dirtree => dirtree_update_inode t' inum off v) l = l.
(* hint proof tokens: 46 *)
Proof.
    induction l; simpl; intros; eauto.
    destruct a; simpl in *.
    rewrite dirtree_update_inode_absent; eauto.
    rewrite IHl; eauto.
  Qed.
Lemma tree_inodes_distinct_not_in_tail : forall l d n inum a,
    In inum (tree_inodes d) ->
    tree_inodes_distinct (TreeDir n ((a, d) :: l)) ->
    ~ In inum (concat (map (fun e : string * dirtree => tree_inodes (snd e)) l)).
(* hint proof tokens: 184 *)
Proof.
    induction l; simpl; eauto.
    intros. destruct a; simpl in *.
    inversion H0; subst.

    intro H'; apply in_app_or in H'; destruct H'.
    rewrite app_assoc in H4. apply NoDup_app_l in H4.
    eapply not_In_NoDup_app. 2: eauto. all: eauto.
    eapply IHl; eauto.
    unfold tree_inodes_distinct; simpl.
    constructor.
    intro; apply H3.
    apply in_app_or in H2. intuition eauto.

    apply NoDup_app_comm in H4. rewrite <- app_assoc in H4.
    apply NoDup_app_comm in H4. apply NoDup_app_l in H4.
    apply NoDup_app_comm in H4. eauto.

    Unshelve. eauto.
  Qed.
Lemma tree_inodes_distinct_not_this_child : forall n s d l pathname inum f,
    tree_inodes_distinct (TreeDir n ((s, d) :: l)) ->
    find_subtree pathname (TreeDir n l) = Some (TreeFile inum f) ->
    ~ In inum (tree_inodes d).
Proof.
(* original proof tokens: 60 *)
intros.
unfold tree_inodes_distinct in H.
simpl in H.
intro Hc.
apply find_subtree_inum_present in H0.
destruct H.
eapply not_In_NoDup_app. 2: eauto. all: eauto.
(* No more tactics to try *)
Admitted.

Hint Resolve tree_inodes_distinct_not_in_tail.
Hint Resolve tree_inodes_distinct_not_this_child.
Lemma tree_inodes_distinct_next : forall n s d l,
    tree_inodes_distinct (TreeDir n ((s, d) :: l)) ->
    tree_inodes_distinct (TreeDir n l).
(* hint proof tokens: 71 *)
Proof.
    unfold tree_inodes_distinct; simpl; intros.
    rewrite cons_app in *.
    apply NoDup_app_comm in H. rewrite <- app_assoc in H.
    apply NoDup_app_comm in H. apply NoDup_app_l in H.
    apply NoDup_app_comm in H; eauto.
  Qed.
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
induction pathname; intros; simpl in *.
(* No more tactics to try *)
Admitted.

Theorem dirtree_update_inode_oob : forall pathname tree inum off f v,
    tree_inodes_distinct tree ->
    tree_names_distinct tree ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    ~ off < length (DFData f) ->
    dirtree_update_inode tree inum off v = tree.
(* hint proof tokens: 233 *)
Proof.
    induction pathname; simpl; intros.
    - inversion H1; subst; simpl.
      destruct (addr_eq_dec inum inum); try congruence.
      rewrite updN_oob by ( apply not_lt; auto ).
      destruct f; auto.
    - destruct tree; simpl in *; try congruence.
      f_equal.
      induction l; simpl in *; try congruence.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst; eauto.
      + erewrite IHpathname; eauto.
        f_equal.
        inversion H0. inversion H6.
        inversion H.
        rewrite dirtree_update_inode_absent'; eauto.
        apply find_subtree_inum_present in H1; simpl in *.
        eapply tree_inodes_distinct_not_in_tail; eauto.
      + rewrite dirtree_update_inode_absent.
        rewrite IHl; eauto.
        eapply tree_inodes_distinct_not_this_child with (pathname := a :: pathname).
        2: apply H1.
        eauto.
  Qed.
Lemma rep_tree_inodes_distinct : forall tree F fsxp Ftop m ilist frees ms sm,
    (F * rep fsxp Ftop tree ilist frees ms sm)%pred m ->
    tree_inodes_distinct tree.
(* hint proof tokens: 162 *)
Proof.
    unfold rep, tree_inodes_distinct; intros.
    destruct_lift H.
    eapply ListPred.listpred_nodup_F.
    apply addr_eq_dec.
    apply ptsto_conflict.
    eapply pimpl_apply. 2: apply H1.

    cancel. instantiate (F0 := (dummy1 * Ftop)%pred). cancel.
    clear H1.
    induction tree using dirtree_ind2; simpl.
    cancel.
    unfold tree_dir_names_pred. cancel. clear H4.
    induction tree_ents; simpl.
    - cancel.
    - inversion H0.
      destruct a.
      rewrite H3; simpl.
      rewrite ListPred.listpred_app.
      rewrite IHtree_ents; eauto.
  Qed.
Lemma find_dirlist_tree_inodes: forall elem name d dnum,
    tree_names_distinct (TreeDir dnum elem) ->
    find_dirlist name elem = Some d ->
    In (dirtree_inum d) (dirlist_combine tree_inodes elem).
(* hint proof tokens: 169 *)
Proof.
    induction elem; intros.
    - simpl in *. inversion H0.
    - rewrite dirlist_combine_app.
      destruct a.
      destruct (string_dec s name); subst.
      + rewrite in_app_iff.
        left.
        simpl in H0.
        destruct (string_dec name name); try congruence; subst.
        inversion H0; subst.
        simpl.
        rewrite app_nil_r; simpl.
        unfold tree_inodes; simpl.
        destruct d; subst; simpl.
        left; eauto.
        left; eauto.
      + rewrite in_app_iff.
        right.
        eapply IHelem; eauto.
        rewrite find_dirlist_ne in H0; eauto.
        inversion H. simpl in H4. eauto.
  Qed.
Lemma tree_inodes_distinct_delete: forall elem name dnum d n inum, 
    tree_names_distinct (TreeDir dnum elem) ->
    tree_inodes_distinct (TreeDir dnum elem) ->
    find_dirlist name elem = Some d ->
    dirtree_inum d = n ->
    In inum (dirlist_combine tree_inodes (delete_from_list name elem)) ->
    inum <> n.
Proof.
(* skipped proof tokens: 454 *)
Admitted.
Lemma tree_inodes_distinct_elem: forall a n l subtree,
    tree_inodes_distinct (TreeDir n l) ->
    find_subtree [a] (TreeDir n l) = Some subtree ->
    tree_inodes_distinct subtree.
Proof.
(* skipped proof tokens: 110 *)
Admitted.
Lemma tree_inodes_distinct_subtree : forall path tree subtree,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    find_subtree path tree = Some subtree ->
    tree_inodes_distinct subtree.
Proof.
(* skipped proof tokens: 252 *)
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
(* skipped proof tokens: 445 *)
Admitted.
Lemma tree_inodes_distinct_update_subtree': forall pathname tree subtree d,
    tree_names_distinct tree ->
    find_subtree pathname tree = Some d ->
    incl (tree_inodes subtree) (tree_inodes (update_subtree pathname subtree tree)).
(* hint proof tokens: 234 *)
Proof.
    induction pathname; intros; subst; simpl.
    - apply incl_refl.
    - destruct tree.
      + simpl in H0. exfalso. inversion H0.
      + induction l; simpl; eauto.
        -- 
          simpl in H0. exfalso. inversion H0.
        -- 
          destruct a0; simpl in *.
          {
            destruct (string_dec s a); subst.
            - rewrite update_subtree_notfound.
              eapply IHpathname with (tree := d0) (subtree := subtree) in H0 as H0; eauto.
              repeat rewrite cons_app with (l := app _ _).
              eapply incl_appr; eauto.
              eapply incl_appl; eauto.
              inversion H. inversion H4. eauto.
            - repeat rewrite cons_app with (l := app _ _).
              eapply incl_app_commr.
              rewrite <- app_assoc.
              eapply incl_appr; eauto.
              eapply incl_app_commr.
              eapply IHl; eauto.  
          }
  Qed.
Lemma tree_inodes_in_update_subtree_child: forall pathname subtree inum tree d,
    tree_names_distinct tree ->
    In inum (tree_inodes subtree) ->
    find_subtree pathname tree = Some d ->
    In inum (tree_inodes (update_subtree pathname subtree tree)).
(* hint proof tokens: 45 *)
Proof.
    intros.
    eapply In_incl with (l1 := (tree_inodes subtree)); eauto.
    eapply tree_inodes_distinct_update_subtree'; eauto.
  Qed.
Lemma leaf_in_inodes_parent : forall path name n l subtree_base d,
    tree_names_distinct (TreeDir n l) ->
    find_subtree [name] (TreeDir n l) = Some subtree_base ->
    find_subtree path subtree_base = Some d ->
    In (dirtree_inum d) (dirlist_combine tree_inodes l).
Proof.
(* skipped proof tokens: 162 *)
Admitted.
Lemma tree_inodes_not_distinct: forall l n s f suffix,
    tree_names_distinct (TreeDir n l) ->
    tree_inodes_distinct (TreeDir n l) ->
    find_subtree (s :: suffix) (TreeDir n l) = Some f ->
    dirtree_inum (TreeDir n l) = dirtree_inum f ->
    False.
Proof.
(* skipped proof tokens: 83 *)
Admitted.
Lemma tree_inodes_in_update_subtree_oob: forall dstpath dstnum dstents tree subtree suffix inum f,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    find_subtree dstpath tree = Some (TreeDir dstnum dstents) ->
    find_subtree suffix tree = Some (TreeFile inum f) ->
    In inum (tree_inodes tree) ->
    (~ pathname_prefix dstpath suffix) ->
    In inum (tree_inodes (update_subtree dstpath subtree tree)).
(* hint proof tokens: 718 *)
Proof.
    induction dstpath; intros; subst; simpl.
    - exfalso. apply H4. eapply pathname_prefix_nil.
    - destruct tree; eauto.
      induction l; subst.
      + simpl in *; eauto.
      + destruct a0; simpl in *. 
      {
        destruct (string_dec s a); subst.
        - 
          rewrite update_subtree_notfound. right.
          apply in_or_app.
          destruct suffix.
          simpl in H2. inversion H2; eauto.
          destruct (string_dec a s); subst.
          + left. eapply IHdstpath; eauto.
            simpl in H2.
            destruct (string_dec s s); subst; try congruence.
            eassumption.
            simpl in H2. inversion H2; eauto.
            destruct (string_dec s s); subst; try congruence.
            replace inum with (dirtree_inum ((TreeFile inum f))).
            eapply find_subtree_inum_present; eauto.
            eauto.
            rewrite cons_app in H4.
            rewrite cons_app with (l := suffix) in H4.
            erewrite <- pathname_prefix_trim in H4; eauto.
          + intuition; subst.
            exfalso. eapply tree_inodes_not_distinct with (n := inum) (l := ((a,d)::l)); eauto.
            right.
            intuition.
            eapply in_app_or in H5.
            intuition.
            clear IHdstpath. clear IHl.
            inversion H0. clear H7. clear H6. clear H5.
            erewrite find_subtree_head_ne_pn in H2.
            eapply find_subtree_inum_present in H2 as H2'. simpl in H2'.
            intuition; subst.
            exfalso. eapply tree_inodes_not_distinct with (n := inum) (l := l); eauto.
            congruence.
            eapply pathname_prefix_head_neq with (a := a); eauto.
          + eapply tree_names_distinct_head_name; eauto.
        - intuition.
          eapply in_app_or in H5.
          intuition.
          edestruct IHl; eauto.
          {
            destruct (pathname_decide_prefix [s] suffix); subst.
            + deex.
              inversion H0. clear H7. clear H6. clear H5. 
              exfalso.
              clear IHl. clear IHdstpath.
              rewrite <- cons_app in H2.
              rewrite find_subtree_head_pn in H2.
              eapply find_subtree_inum_present in H2 as H2'; eauto.
              simpl in H2'.
              rewrite app_nil_r in *.
              intuition; subst.
              eapply tree_inodes_not_distinct with (n := inum) (l := [(s, d)]); eauto.
              eapply tree_names_distinct_head; eauto.
              eapply tree_inodes_distinct_head; eauto.
              eapply not_In_NoDup_app in H8; eauto.
              eapply pathname_prefix_head.
            + destruct suffix.
              - simpl in *. inversion H2.
              - erewrite find_subtree_head_ne_pn in H2; eauto.
                congruence.
                eapply pathname_prefix_neq; eauto.
          }
     }
  Qed.
Lemma tree_inodes_in_add_to_dir_oob: forall pn inum tree subtree dstname f,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    find_subtree pn tree = Some (TreeFile inum f) ->
    (~pathname_prefix [dstname] pn) ->
    In inum (tree_inodes (add_to_dir dstname subtree tree)).
Proof.
(* skipped proof tokens: 546 *)
Admitted.
Lemma tree_inodes_in_delete_from_list_oob: forall pn srcents inum f srcnum srcname,
    tree_names_distinct (TreeDir srcnum srcents) ->
    tree_inodes_distinct (TreeDir srcnum srcents) ->
    find_subtree pn (TreeDir srcnum srcents) = Some (TreeFile inum f) ->
    (~ pathname_prefix [srcname] pn) -> 
    In inum (tree_inodes (TreeDir srcnum srcents)) ->
    In inum (tree_inodes (TreeDir srcnum (delete_from_list srcname srcents))).
Proof.
(* skipped proof tokens: 342 *)
Admitted.
Lemma tree_inodes_in_delete_from_dir_oob: forall pn srcents inum f srcnum srcname,
    tree_names_distinct (TreeDir srcnum srcents) ->
    tree_inodes_distinct (TreeDir srcnum srcents) ->
    find_subtree pn (TreeDir srcnum srcents) = Some (TreeFile inum f) ->
    (~ pathname_prefix [srcname] pn) -> 
    In inum (tree_inodes (TreeDir srcnum srcents)) ->
    In inum (tree_inodes (delete_from_dir srcname (TreeDir srcnum srcents))).
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma tree_inodes_incl_delete_from_list : forall name l,
    incl (dirlist_combine tree_inodes (delete_from_list name l))
         (dirlist_combine tree_inodes l).
(* hint proof tokens: 65 *)
Proof.
    induction l; simpl; eauto.
    eapply incl_refl.
    destruct a.
    destruct (string_dec s name); subst.
    - eapply incl_appr; apply incl_refl.
    - simpl.
      eapply incl_app2r. eauto.
  Qed.
Lemma tree_inodes_nodup_delete_from_list : forall name l,
    NoDup (dirlist_combine tree_inodes l) ->
    NoDup (dirlist_combine tree_inodes (delete_from_list name l)).
Proof.
(* skipped proof tokens: 72 *)
Admitted.
Lemma tree_inodes_distinct_delete_from_list : forall l n name,
    tree_inodes_distinct (TreeDir n l) ->
    tree_inodes_distinct (TreeDir n (delete_from_list name l)).
(* hint proof tokens: 73 *)
Proof.
    unfold tree_inodes_distinct; simpl; intros.
    inversion H; subst.
    constructor.
    - contradict H2.
      eapply In_incl; eauto.
      eapply tree_inodes_incl_delete_from_list.
    - eapply tree_inodes_nodup_delete_from_list; eauto.
  Qed.
Lemma tree_inodes_find_subtree_incl : forall pathname t subtree,
    find_subtree pathname t = Some subtree ->
    incl (tree_inodes subtree) (tree_inodes t).
Proof.
(* skipped proof tokens: 128 *)
Admitted.
Lemma tree_inodes_distinct_prune: forall srcbase dnum tree_elem srcnum srcents srcname,
    tree_names_distinct (TreeDir dnum tree_elem) ->
    tree_inodes_distinct (TreeDir dnum tree_elem) ->
    find_subtree srcbase (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ->
    tree_inodes_distinct
      (tree_prune srcnum srcents srcbase srcname (TreeDir dnum tree_elem)).
(* hint proof tokens: 89 *)
Proof.
    intros.
    unfold tree_prune, delete_from_dir.
    eapply tree_inodes_distinct_update_subtree; eauto.
    eapply tree_inodes_distinct_delete_from_list; eauto.
    eapply tree_inodes_distinct_subtree; eauto.
    simpl.
    eapply incl_cons2.
    eapply tree_inodes_incl_delete_from_list; eauto.
  Qed.
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
(* hint proof tokens: 3388 *)
Proof.
    intros.
    destruct (pathname_decide_prefix cwd pathname').
    + 
      deex.
      erewrite find_subtree_app in H3.
      2: eauto.
      eapply tree_inodes_in_update_subtree_child; eauto.
      unfold tree_prune in H7.
      destruct (pathname_decide_prefix dstbase suffix).
      ++
        deex.
        eapply tree_inodes_in_update_subtree_child; eauto.
        eapply tree_names_distinct_prune_subtree'; eauto.
        eapply tree_names_distinct_subtree; eauto.
        rewrite <- pathname_prefix_trim in H2. 
        rewrite <- pathname_prefix_trim in H2. 
        
        {
          destruct (pathname_decide_prefix dstbase srcbase).
          + 
            deex.
            eapply find_subtree_app' in H3. deex.
            erewrite find_subtree_update_subtree_child in H7; eauto.
            inversion H7. subst.
            destruct (pathname_decide_prefix suffix suffix0).
            - 
              deex.
              destruct (pathname_decide_prefix [srcname] suffix1).
              deex.
              ++ 
                 rewrite <- pathname_prefix_trim in H1. 
                 rewrite <- app_assoc in H1.
                 rewrite <- pathname_prefix_trim in H1.
                 rewrite <- pathname_prefix_trim in H1.
                 exfalso. apply H1. eapply pathname_prefix_head.
              ++  
                eapply find_subtree_app' in H5; eauto. deex.
                rewrite H11 in H8. inversion H8. subst. clear H8.
                erewrite find_subtree_app in H9; eauto.
                eapply find_subtree_inum_present in H9 as H9'; eauto.
                eapply tree_inodes_in_add_to_dir_oob with (pn := suffix++suffix1); eauto.
                eapply tree_names_distinct_update_subtree; eauto.
                eapply tree_names_distinct_subtree in H11; eauto.
                eapply tree_names_distinct_subtree; eauto.
                eapply tree_names_distinct_delete_from_list; eauto.
                eapply tree_names_distinct_subtree in H12; eauto.
                eapply tree_names_distinct_subtree in H11; eauto.
                eapply tree_names_distinct_subtree; eauto.
                eapply tree_inodes_distinct_update_subtree; eauto.
                eapply tree_names_distinct_subtree in H11; eauto.
                eapply tree_names_distinct_subtree; eauto.
                eapply tree_inodes_distinct_subtree in H11; eauto.
                eapply tree_names_distinct_subtree; eauto.
                eapply tree_inodes_distinct_subtree; eauto.
                eapply tree_inodes_distinct_delete_from_list; eauto.
                eapply tree_inodes_distinct_subtree in H12; eauto.
                eapply tree_names_distinct_subtree in H11; eauto.
                eapply tree_names_distinct_subtree; eauto.
                eapply tree_inodes_distinct_subtree in H11; eauto.
                eapply tree_names_distinct_subtree; eauto.
                eapply tree_inodes_distinct_subtree; eauto.
                
                simpl.
                eapply incl_cons2.
                eapply tree_inodes_incl_delete_from_list.
                erewrite find_subtree_app 
                    with (subtree := (TreeDir srcnum (delete_from_list srcname srcents))); eauto.
                destruct suffix1.
                simpl in *. inversion H9.
                erewrite find_subtree_delete_ne'; eauto.
                assert (tree_names_distinct (TreeDir srcnum srcents)).
                eapply tree_names_distinct_subtree in H12; eauto.
                eapply tree_names_distinct_subtree in H11; eauto.
                eapply tree_names_distinct_subtree; eauto.
                inversion H5; eauto.
                intro. subst.
                eapply H3. exists suffix1.  rewrite cons_app. congruence.
            - 
                eapply find_subtree_app' in H5; eauto. deex.
                rewrite H11 in H8. inversion H8. subst. clear H8.
                destruct (pathname_decide_prefix [dstname] suffix).
                ++ 
                  deex.
                  eapply tree_inodes_in_add_to_dir_oob with (pn := suffix0); eauto.
                  clear H10. clear H7.
                  eapply tree_names_distinct_update_subtree; eauto.
                  eapply tree_names_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_names_distinct_delete_from_list; eauto.
                  eapply tree_names_distinct_subtree in H12; eauto.
                  eapply tree_names_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_update_subtree; eauto.
                  eapply tree_names_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_delete_from_list; eauto.
                  eapply tree_inodes_distinct_subtree in H12; eauto.
                  eapply tree_names_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_subtree; eauto.
                  simpl.
                  eapply incl_cons2.
                  eapply tree_inodes_incl_delete_from_list.
                  erewrite find_subtree_update_subtree_ne_path; eauto.
                  eapply tree_names_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  intro. eapply H3. unfold pathname_prefix in H5. deex.
                  eexists suffix. f_equal.
                  destruct suffix0.
                  simpl in H9. eapply find_subtree_app' in H12. deex.
                  destruct subtree_base. simpl in H12. inversion H12. 
                  inversion H9.
                  intro. eapply H3.  unfold pathname_prefix in H5. deex.
                  rewrite <- cons_app in H5.
                  rewrite cons_app in H5.
                  rewrite <- app_assoc in H5.
                  rewrite <- cons_app in H5.
                  inversion H5. subst. clear H5.
                  exfalso. eapply H2. apply pathname_prefix_head.
                ++
                  
                  eapply tree_inodes_in_add_to_dir_oob with (pn := suffix0); eauto.
                  eapply tree_names_distinct_update_subtree; eauto.
                  eapply tree_names_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_names_distinct_delete_from_list; eauto.
                  eapply tree_names_distinct_subtree in H12; eauto.
                  eapply tree_names_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_update_subtree; eauto.
                  eapply tree_names_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_delete_from_list; eauto.
                  eapply tree_inodes_distinct_subtree in H12; eauto.
                  eapply tree_names_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_subtree in H11; eauto.
                  eapply tree_names_distinct_subtree; eauto.
                  eapply tree_inodes_distinct_subtree; eauto.
                  simpl.
                  eapply incl_cons2.
                  eapply tree_inodes_incl_delete_from_list.
                  erewrite find_subtree_update_subtree_oob; eauto.
          + 
            destruct (pathname_decide_prefix srcbase dstbase).
            - 
              deex.
              destruct (pathname_decide_prefix [srcname] suffix).
              ++ 
                deex.
                rewrite <- pathname_prefix_trim in H1.
                rewrite <- app_assoc in H1.
                rewrite <- pathname_prefix_trim in H1.
                rewrite <- app_assoc in H1.
                exfalso. apply H1. apply pathname_prefix_head.
              ++ 
                eapply find_subtree_app' in H3. deex.
                erewrite find_subtree_app in H7; eauto.
                eapply find_subtree_app' in H10. deex.
                destruct (pathname_decide_prefix [srcname] suffix).
                deex.
                rewrite <- pathname_prefix_trim in H1. 
                rewrite <- app_assoc in H1.
                rewrite <- pathname_prefix_trim in H1.
                rewrite <- app_assoc in H1.
                exfalso. apply H1. apply pathname_prefix_head.
                rewrite H5 in H10. inversion H10. subst. clear H10.
                rewrite <- pathname_prefix_trim in H1.
                rewrite <- app_assoc in H1.
                rewrite <- pathname_prefix_trim in H1.
                destruct suffix.
                simpl in H7.
                rewrite app_nil_r in *. exfalso. apply H8. 
                eexists []. rewrite app_nil_r in *. eauto.
                erewrite find_subtree_delete_ne in H7.
                rewrite H7 in H12. inversion H12; subst. clear H12.
                eapply tree_inodes_in_add_to_dir_oob; eauto.
                eapply tree_names_distinct_subtree in H7; eauto.
                eapply tree_names_distinct_subtree in H5; eauto.
                eapply tree_names_distinct_subtree; eauto.
                eapply tree_inodes_distinct_subtree in H7; eauto.
                eapply tree_names_distinct_subtree in H5; eauto.
                eapply tree_names_distinct_subtree; eauto.
                eapply tree_inodes_distinct_subtree in H5; eauto.
                eapply tree_names_distinct_subtree; eauto.
                eapply tree_inodes_distinct_subtree; eauto.
                assert (tree_names_distinct (TreeDir srcnum srcents)).
                eapply tree_names_distinct_subtree in H5; eauto.
                eapply tree_names_distinct_subtree; eauto.
                inversion H10; eauto.
                intro. subst. eapply H3. exists suffix.
                rewrite cons_app. f_equal.
            -  
              eapply find_subtree_app' in H3. deex.
              rewrite find_subtree_update_subtree_ne_path in H7.  
              rewrite H7 in H10. inversion H10. subst. clear H10.
              destruct (pathname_decide_prefix [dstname] suffix0).
              ++ deex. exfalso. eapply H2. eapply pathname_prefix_head.
              ++ 
                eapply tree_inodes_in_add_to_dir_oob; eauto.
                eapply tree_names_distinct_subtree in H7; eauto.
                eapply tree_names_distinct_subtree; eauto.
                eapply tree_inodes_distinct_subtree in H7; eauto.
                eapply tree_names_distinct_subtree; eauto.
                eapply tree_inodes_distinct_subtree; eauto.
              ++ eapply tree_names_distinct_subtree; eauto.
              ++ eapply pathname_prefix_neq; eauto.
              ++ eapply pathname_prefix_neq; eauto.
        }
      ++ 
        
        unfold tree_graft.
        eapply tree_inodes_in_update_subtree_oob with (suffix := suffix) (f := f); eauto.
        eapply tree_names_distinct_prune_subtree'; eauto.
        eapply tree_names_distinct_subtree; eauto.
        eapply tree_inodes_distinct_prune; eauto.
        eapply tree_names_distinct_subtree; eauto.
        eapply tree_inodes_distinct_subtree; eauto.
        {
          unfold tree_prune.
          destruct (pathname_decide_prefix srcbase suffix).
          + deex.
            erewrite find_subtree_app; eauto.
            destruct (pathname_decide_prefix [srcname] suffix0).
            deex.
            rewrite <- pathname_prefix_trim in H1. 
            rewrite <- pathname_prefix_trim in H1. 
            exfalso. apply H1. apply pathname_prefix_head.
            {
              destruct suffix0.
              + 
                rewrite app_nil_r in *.
                rewrite H5 in H3.
                inversion H3.
              +
                erewrite find_subtree_delete_ne.
                erewrite find_subtree_app in H3; eauto.
                 eapply tree_names_distinct_subtree in H5; eauto.
                inversion H5; eauto.
                eapply tree_names_distinct_subtree; eauto.
                intro. eapply H9. eexists suffix0. subst.
                rewrite cons_app; eauto.
            }
          + erewrite find_subtree_update_subtree_oob; eauto.
        }
        destruct (pathname_decide_prefix srcbase suffix).
        -- 
          deex.
          unfold tree_prune.
          eapply tree_inodes_in_update_subtree_child; eauto.
          eapply tree_names_distinct_subtree; eauto.
          {
          destruct (pathname_decide_prefix [srcname] suffix0).
          + deex.
            rewrite <- pathname_prefix_trim in H1. 
            rewrite <- pathname_prefix_trim in H1. 
            exfalso. apply H1. apply pathname_prefix_head.
      +
            eapply tree_inodes_in_delete_from_dir_oob; eauto.
            eapply tree_names_distinct_subtree in H5; eauto.
            eapply tree_names_distinct_subtree; eauto.
            eapply tree_inodes_distinct_subtree in H5; eauto.
            eapply tree_names_distinct_subtree; eauto.
            eapply tree_inodes_distinct_subtree; eauto.
            erewrite find_subtree_app in H3; eauto.
            eapply pathname_prefix_neq; eauto.
            erewrite find_subtree_app in H3; eauto.
            replace inum with (dirtree_inum ((TreeFile inum f))).
            eapply find_subtree_inum_present; eauto.
            simpl; eauto.
           }
        -- 
          unfold tree_prune.
          eapply tree_inodes_in_update_subtree_oob with (suffix := suffix); eauto.
          eapply tree_names_distinct_subtree; eauto.
          eapply tree_inodes_distinct_subtree; eauto.
          replace inum with (dirtree_inum ((TreeFile inum f))).
          eapply find_subtree_inum_present; eauto.
          simpl; eauto.
          eapply pathname_prefix_neq; eauto.
        -- 
          eapply pathname_prefix_neq; eauto.
    + 
      eapply find_subtree_update_subtree_oob in H3 as H3'.
      replace inum with (dirtree_inum ((TreeFile inum f))).
      eapply find_subtree_inum_present; eauto.
      simpl; eauto.
      eassumption.
  Qed.
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
(* skipped proof tokens: 210 *)
Admitted.
Definition conflicting (p q : Prop) := (p -> ~ q) /\ (q -> ~ p).
Definition xor (p q : Prop) := (p /\ ~ q) \/ (q /\ ~ p).
Lemma NoDup_In_conflicting : forall T (l1 l2 : list T) x,
    NoDup (l1 ++ l2) ->
    conflicting (In x l1) (In x l2).
(* hint proof tokens: 37 *)
Proof.
    unfold conflicting; split; intros; eapply not_In_NoDup_app; eauto.
    eapply NoDup_app_comm; eauto.
  Qed.
Lemma tree_inodes_after_prune' : forall srcpath t srcnum srcents srcname mvtree,
    tree_names_distinct t ->
    find_subtree srcpath t = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some mvtree ->
    permutation addr_eq_dec
      (tree_inodes mvtree ++ tree_inodes (tree_prune srcnum srcents srcpath srcname t))
      (tree_inodes t).
Proof.
(* skipped proof tokens: 566 *)
Admitted.
Lemma tree_inodes_after_prune : forall srcpath t srcnum srcents srcname mvtree inum,
    tree_inodes_distinct t ->
    tree_names_distinct t ->
    find_subtree srcpath t = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some mvtree ->
    conflicting (In inum (tree_inodes mvtree))
                (In inum (tree_inodes (tree_prune srcnum srcents srcpath srcname t))).
Proof.
(* skipped proof tokens: 69 *)
Admitted.
Lemma tree_inodes_after_graft' : forall dstpath t dstnum dstents dstname mvtree,
    tree_names_distinct t ->
    find_subtree dstpath t = Some (TreeDir dstnum dstents) ->
    permutation
      addr_eq_dec
      (tree_inodes (tree_graft dstnum dstents dstpath dstname mvtree t))
      ((tree_inodes mvtree) ++
       (tree_inodes (tree_prune dstnum dstents dstpath dstname t))).
(* hint proof tokens: 534 *)
Proof.
    unfold tree_graft, tree_prune.
    induction dstpath; simpl; intros.
    - inversion H0; clear H0; subst.
      induction dstents; simpl; intros.
      + rewrite app_nil_r. rewrite cons_app.
        apply permutation_app_comm.
      + destruct a.
        destruct (string_dec s dstname); subst.
        * simpl. rewrite cons_app. rewrite cons_app with (l := dirlist_combine _ _).
          repeat rewrite app_assoc. apply permutation_app_split.
          2: apply permutation_refl.
          apply permutation_app_comm.
        * simpl. rewrite cons_app. rewrite cons_app with (l := app _ _).
          eapply permutation_trans. apply permutation_app_comm. rewrite <- app_assoc.
          eapply permutation_trans. 2: rewrite app_assoc. 2: apply permutation_app_comm.
          rewrite <- app_assoc.
          apply permutation_app_split. apply permutation_refl.
          eapply permutation_trans. apply permutation_app_comm.
          eapply permutation_trans. 2: apply permutation_app_comm.
          rewrite <- app_assoc.
          eauto.
    - destruct t; simpl in *; try congruence.
      induction l; simpl in *; try congruence; intros.
      destruct a0; simpl.
      destruct (string_dec s a); subst; simpl in *.
      + inversion H; inversion H4; subst.
        repeat rewrite update_subtree_notfound by auto.
        rewrite cons_app. rewrite cons_app with (l := app _ _).
        eapply permutation_trans. 2: apply permutation_app_comm. rewrite <- app_assoc.
        apply permutation_app_split. apply permutation_refl.
        eapply permutation_trans. 2: apply permutation_app_comm. rewrite app_assoc.
        apply permutation_app_split. 2: apply permutation_refl.
        destruct (string_dec a a); try congruence.
        eapply IHdstpath; eauto.
      + rewrite cons_app. rewrite cons_app with (l := app _ _).
        eapply permutation_trans. apply permutation_app_comm. rewrite <- app_assoc.
        rewrite app_assoc with (l := tree_inodes mvtree).
        eapply permutation_trans. 2: apply permutation_app_comm. rewrite <- app_assoc.
        apply permutation_app_split. apply permutation_refl.
        eapply permutation_trans. apply permutation_app_comm.
        eapply permutation_trans. 2: apply permutation_app_comm. rewrite <- app_assoc.
        destruct (string_dec s a); try congruence.
        eauto.
  Qed.
Lemma tree_inodes_tree_graft_incl_count : forall dstpath t dstnum dstents dstname mvtree,
    tree_names_distinct t ->
    find_subtree dstpath t = Some (TreeDir dstnum dstents) ->
    incl_count addr_eq_dec
      (tree_inodes (tree_graft dstnum dstents dstpath dstname mvtree t))
      (tree_inodes t ++ tree_inodes mvtree).
Proof.
(* skipped proof tokens: 540 *)
Admitted.
Lemma tree_inodes_after_graft : forall dstpath t dstnum dstents dstname mvtree inum,
    NoDup (tree_inodes t ++ tree_inodes mvtree) ->
    tree_names_distinct t ->
    find_subtree dstpath t = Some (TreeDir dstnum dstents) ->
    In inum (tree_inodes (tree_graft dstnum dstents dstpath dstname mvtree t)) ->
    xor (In inum (tree_inodes mvtree))
        (In inum (tree_inodes (tree_prune dstnum dstents dstpath dstname t))).
Proof.
(* skipped proof tokens: 174 *)
Admitted.
Lemma tree_inodes_nodup_delete_from_list' : forall srcpath srcname srcents srcnum t mvtree top_extras,
    forall (Hd : tree_names_distinct t),
    find_subtree srcpath t = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some mvtree ->
    NoDup (top_extras ++ tree_inodes t) ->
    NoDup (top_extras ++ tree_inodes (tree_prune srcnum srcents srcpath srcname t) ++ tree_inodes mvtree).
(* hint proof tokens: 506 *)
Proof.
    induction srcpath; simpl; intros.
    - inversion H; clear H; subst.
      simpl in *.

      match goal with
      | [ H : NoDup (top_extras ++ ?n :: ?x) |- NoDup (top_extras ++ ?n :: ?y) ] =>
        cut (forall extra_inodes, NoDup (n :: extra_inodes ++ x) -> NoDup (n :: extra_inodes ++ y));
        [ intro Hcut; specialize (Hcut top_extras); nodupapp
        | intros ]
      end.

      clear H1.
      generalize dependent extra_inodes.
      induction srcents; simpl in *; try congruence; intros.
      destruct a.
      destruct (string_dec s srcname); subst; simpl.
      + inversion H0; clear H0; subst.
        nodupapp.
      + rewrite app_assoc. rewrite app_assoc. rewrite <- app_assoc.
        eapply IHsrcents; eauto. nodupapp.
    - destruct t; simpl in *; try congruence.

      match goal with
      | [ H : NoDup (top_extras ++ ?n :: ?x) |- NoDup (top_extras ++ ?n :: ?y) ] =>
        cut (forall extra_inodes, NoDup (n :: extra_inodes ++ x) -> NoDup (n :: extra_inodes ++ y));
        [ intro Hcut; specialize (Hcut top_extras); nodupapp
        | intros ]
      end.

      clear H1.
      generalize dependent extra_inodes.
      induction l; simpl in *; try congruence; intros.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst; simpl.
      + rewrite update_subtree_notfound.
        rewrite cons_app in H2. rewrite app_assoc in H2. rewrite app_assoc in H2. apply NoDup_app_comm in H2.
        rewrite app_assoc in H2.
        eapply IHsrcpath in H2; eauto.
        unfold tree_prune in H2.
        simpl in *.
        nodupapp.
        inversion Hd; inversion H5; eauto.
      + rewrite app_assoc in H2.
        eapply IHl in H2; eauto.
        nodupapp.
  Unshelve.
    all: exact addr_eq_dec.
  Qed.
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
(* skipped proof tokens: 107 *)
Admitted.
Lemma tree_inodes_incl_delete_from_dir : forall pathname dnum tree_elem name pnum pelem,
    tree_names_distinct (TreeDir dnum tree_elem) ->
    tree_inodes_distinct (TreeDir dnum tree_elem) ->
    find_subtree pathname (TreeDir dnum tree_elem) = Some (TreeDir pnum pelem) ->
    incl (tree_inodes (update_subtree pathname (delete_from_dir name (TreeDir pnum pelem)) (TreeDir dnum tree_elem)))
         (tree_inodes (TreeDir dnum tree_elem)).
Proof.
(* skipped proof tokens: 329 *)
Admitted.
Lemma find_subtree_tree_inodes_distinct: forall pn t subtree,
      tree_inodes_distinct t ->
      find_subtree pn t = Some subtree ->
      tree_inodes_distinct subtree.
(* hint proof tokens: 110 *)
Proof.
    induction pn; intros; simpl in *.
    - congruence.
    - destruct t; try congruence.
      induction l.
      -- simpl in *; try congruence.
      -- destruct a0; subst; simpl in *.
        destruct (string_dec s a); subst; simpl in *.
        + eapply IHpn. 2: eauto.
          eapply tree_inodes_distinct_child; eauto.
        + eapply IHl; eauto.
  Qed.
Lemma rep_tree_distinct_impl : forall fsxp Ftop tree ilist frees ms sm,
    rep fsxp Ftop tree ilist frees ms sm =p=> rep fsxp Ftop tree ilist frees ms sm *
      [[ tree_names_distinct tree ]] *
      [[ tree_inodes_distinct tree ]].
(* hint proof tokens: 79 *)
Proof.
    unfold pimpl; intros.
    assert ((emp * rep fsxp Ftop tree ilist frees ms sm)%pred m) by ( pred_apply; cancel ).
    eapply rep_tree_names_distinct in H0 as H0'.
    eapply rep_tree_inodes_distinct in H0 as H0''.
    pred_apply; cancel.
  Qed.
Theorem find_subtree_inode_pathname_unique : forall path1 path2 tree f1 f2,
    tree_inodes_distinct tree ->
    tree_names_distinct tree ->
    find_subtree path1 tree = Some f1 ->
    find_subtree path2 tree = Some f2 -> 
    dirtree_inum f1 = dirtree_inum f2 ->
    path1 = path2.
(* hint proof tokens: 824 *)
Proof.
    induction path1; intros.
    - destruct path2; try congruence.
      destruct tree. simpl in *; try congruence.
      exfalso; eapply tree_inodes_not_distinct; eauto.
      simpl in *; inversion H1; subst; simpl in *; congruence.
    - destruct path2.
      + destruct tree. simpl in *; try congruence.
        exfalso; eapply tree_inodes_not_distinct; eauto.
        simpl in *; inversion H2; subst; simpl in *; congruence.
      + destruct (string_dec a s); subst.
        * f_equal.
          rewrite cons_app in *.
          case_eq (find_subtree [s] tree); intros. destruct d.
         -- erewrite find_subtree_app in * by eauto; simpl in *.
            destruct path1; destruct path2; simpl in *; congruence.
         -- erewrite find_subtree_app in * by eauto.
            eapply IHpath1 with (tree := TreeDir n l); eauto.
            eapply tree_inodes_distinct_subtree; eauto.
            eapply tree_names_distinct_subtree; eauto.
         -- erewrite find_subtree_app_none in * by eauto; congruence.
        * destruct tree. simpl in *; try congruence.
          unfold tree_inodes_distinct in H; simpl in *.
          exfalso.
          induction l; simpl in *; try congruence.
          destruct a0; simpl in *.
          destruct (string_dec s0 a).
          {
            clear IHl.
            apply find_subtree_inum_present in H1.
            destruct (string_dec s0 s); try congruence.
            induction l; simpl in *; try congruence.
            destruct a0; simpl in *.
            destruct (string_dec s1 s).
            {
              apply find_subtree_inum_present in H2.
              rewrite cons_app in H; rewrite app_assoc in H.
              rewrite H3 in *.
              eapply not_In_NoDup_app with (a := dirtree_inum f2). 2: eauto. eauto. eauto.
            }
            eapply IHl; eauto.
            rewrite app_comm_cons in *; eapply NoDup_remove_mid; eauto.
            inversion H0; constructor; eauto; simpl in *.
            inversion H6. inversion H11. eauto.
            rewrite cons_app with (a := s0) in *.
            rewrite cons_app with (a := s1) in *.
            eapply NoDup_remove_mid; eauto.
          }
          destruct (string_dec s0 s).
          {
            clear IHl.
            apply find_subtree_inum_present in H2.
            destruct (string_dec s0 a); try congruence.
            induction l; simpl in *; try congruence.
            destruct a0; simpl in *.
            destruct (string_dec s1 a).
            {
              apply find_subtree_inum_present in H1.
              rewrite cons_app in H; rewrite app_assoc in H.
              rewrite H3 in *.
              eapply not_In_NoDup_app with (a := dirtree_inum f2). 2: eauto. eauto. eauto.
            }
            eapply IHl; eauto.
            rewrite app_comm_cons in *; eapply NoDup_remove_mid; eauto.
            inversion H0; constructor; eauto; simpl in *.
            inversion H6. inversion H11. eauto.
            rewrite cons_app with (a := s0) in *.
            rewrite cons_app with (a := s1) in *.
            eapply NoDup_remove_mid; eauto.
          }
          eapply IHl; eauto.
          inversion H; constructor; eauto.
  Qed.
Theorem dirtree_update_block : forall pathname F0 tree fsxp F ilist freeblocks ms sm inum off v bn m f,
    (F0 * rep fsxp F tree ilist freeblocks ms sm)%pred (list2nmem m) ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist bn inum off ->
    (F0 * rep fsxp F (dirtree_update_inode tree inum off v) ilist freeblocks ms sm)%pred (list2nmem (updN m bn v)).
(* hint proof tokens: 363 *)
Proof.
    intros.
    apply rep_tree_names_distinct in H as Hnames.
    apply rep_tree_inodes_distinct in H as Hinodes.
    unfold rep in *.
    destruct_lift H.
    eapply pimpl_apply; [ | eapply BFILE.rep_safe_used; eauto; pred_apply; cancel ].
    cancel.

    rewrite subtree_extract in H3; eauto.
    remember H3 as H3'; clear HeqH3'.
    erewrite dirtree_update_inode_update_subtree; eauto.
    rewrite <- subtree_absorb; eauto; simpl in *.
    eapply pimpl_apply. 2: destruct_lift H3'; eapply list2nmem_updN; pred_apply; cancel.
    destruct_lift H3.
    eapply pimpl_apply in H2. eapply list2nmem_sel with (i := inum) in H2. 2: cancel.
    rewrite <- H2.
    cancel.

    simpl in *.
    destruct_lift H3'.
    eapply pimpl_apply in H2.
    eapply list2nmem_sel with (i := inum) in H2.
    2: cancel.

    match goal with
    | [ H : _ = selN dummy inum ?def |- _ ] =>
      replace (DFData f) with (BFILE.BFData (selN dummy inum def)); [ | destruct (selN dummy inum def) ]
    end.

    eapply BFILE.block_belong_to_file_bfdata_length; eauto.
    eapply pimpl_apply; [ | apply H ]. cancel.

    inversion H2. subst. simpl. congruence.
  Qed.
Theorem tree_inodes_pathname_exists : forall tree inum,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    In inum (tree_inodes tree) ->
    exists pathname subtree,
    find_subtree pathname tree = Some subtree /\ dirtree_inum subtree = inum.
Proof.
(* skipped proof tokens: 263 *)
Admitted.
Lemma update_subtree_same: forall pn tree subtree,
    tree_names_distinct tree ->
    find_subtree pn tree = Some subtree ->
    update_subtree pn subtree tree = tree.
Proof.
(* skipped proof tokens: 244 *)
Admitted.
