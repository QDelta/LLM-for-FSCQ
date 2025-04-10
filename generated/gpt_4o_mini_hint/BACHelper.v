Require Import String.
Require Import Prog ProgMonad.
Require Import Log.
Require Import Word.
Require Import Lia.
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
Require Import DirTreeDef.
Require Import DirTreeNames.
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import GroupLog.
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import VBConv.
Require Import AsyncFS.
Require Import AByteFile.
Require Import TreeCrash.
Require Import DirSep.
Require Import Rounding.
Require Import TreeSeq.
Require Import AtomicCp.
Import DIRTREE.
Import DTCrash.
Import TREESEQ.
Import ATOMICCP.
Import ListNotations.
Set Implicit Arguments.
Notation tree_rep := ATOMICCP.tree_rep.
Hint Resolve valubytes_ne_O.
Hint Resolve valubytes_ge_O.
Fixpoint dsupd_iter ds bnl vsl:=
match vsl with
| nil => ds
| h::t => match bnl with
               | nil => ds
               | h'::t' => dsupd_iter (dsupd ds h' h) t' t
              end
end.
Fixpoint tsupd_iter ts pathname off vsl:=
match vsl with
| nil => ts
| h::t => tsupd_iter (tsupd ts pathname off h) pathname (S off) t
end.
Definition hpad_length len:=
match (len mod valubytes) with
| O => O
| S _ => valubytes - len mod valubytes
end.
Definition tpad_length l:=
  match l mod valubytes with 
  | O => valubytes
  | S _ => l mod valubytes
  end.
Ltac split_hypothesis_helper:=
  match goal with
  | [ H: exists _, _ |- _ ] => destruct H
  | [ H: _ /\ _ |- _] => destruct H
  end.
Ltac split_hypothesis:= repeat split_hypothesis_helper.
Ltac rewrite_proto:= 
match goal with
| [H: proto_bytefile_valid _ ?pfy |- context[PByFData ?pfy] ] => rewrite H
end.
Ltac length_rewrite_l_helper:= 
  rewrite app_length || rewrite map_length 
  || rewrite concat_hom_length with (k:= valubytes)
  || rewrite merge_bs_length || rewrite valu2list_len
  || rewrite firstn_length_l || rewrite skipn_length
  || rewrite valuset2bytesets_len || rewrite valuset2bytesets_rec_len
  || rewrite length_updN || (rewrite list_split_chunk_length; try rewrite min_l)
  || (rewrite get_sublist_length; try rewrite min_l) || (rewrite combine_length; try rewrite min_l).
Ltac length_rewrite_l:= repeat (length_rewrite_l_helper; simpl); try lia.
Ltac length_rewrite_r_helper:= 
  rewrite app_length || rewrite map_length 
  || rewrite concat_hom_length with (k:= valubytes)
  || rewrite merge_bs_length || rewrite valu2list_len
  || rewrite firstn_length_r || rewrite skipn_length
  || rewrite valuset2bytesets_len || rewrite valuset2bytesets_rec_len
  || rewrite length_updN || (rewrite list_split_chunk_length; try rewrite min_r)
  || (rewrite get_sublist_length; try rewrite min_r) || (rewrite combine_length;  try rewrite min_r).
Ltac length_rewrite_r:= repeat (length_rewrite_r_helper; simpl); try lia.
Ltac length_rewrite_safe_helper:= 
  rewrite app_length || rewrite map_length 
  || rewrite concat_hom_length with (k:= valubytes)
  || rewrite merge_bs_length || rewrite valu2list_len
  || rewrite firstn_length || rewrite skipn_length
  || rewrite valuset2bytesets_len || rewrite valuset2bytesets_rec_len
  || rewrite length_updN || rewrite list_split_chunk_length
  || rewrite get_sublist_length || rewrite combine_length.
Ltac length_rewrite_safe:= repeat (length_rewrite_safe_helper; simpl); try lia.
Opaque LOG.idempred.
Opaque crash_xform.
Lemma concat_valuset2bytesets_map_fstnil_comm: forall l,
 (concat (map valuset2bytesets (map (fun x : valuset => (fst x, [])) l))) =
    map (fun x : byteset => (fst x, [])) (concat (map valuset2bytesets l)).
(* hint proof tokens: 211 *)
Proof.
  intros.
  rewrite concat_map.
  repeat (rewrite map_map; simpl).
  replace  (fun x : valuset => map (fun x0 : byteset => (fst x0, [])) (valuset2bytesets x))
    with ((fun x : valuset => valuset2bytesets (fst x, []))).
  reflexivity.
  apply functional_extensionality; intros.
  replace (map (fun x0 : byteset => (fst x0, [])) (valuset2bytesets x))
  with (map (fun x0 : byte => (x0, nil: list byte)) (map fst (valuset2bytesets x))).
  rewrite mapfst_valuset2bytesets.
  unfold valuset2bytesets; simpl.
  rewrite v2b_rec_nil.
  rewrite l2b_cons_x_nil.
  reflexivity.
  rewrite valu2list_len; reflexivity.
  rewrite map_map; simpl.
  reflexivity.
Qed.
Lemma merge_bs_map_fst: forall l l',
map fst (merge_bs l l') = l.
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_upd_off_tree_rep: forall ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile vs off ,
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname  dstfile) (tsupd ts tmppath off vs).
Proof.
(* original proof tokens: 276 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_pushd_tree_rep: forall ts t Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
   tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) (pushd t ts).
(* hint proof tokens: 118 *)
Proof.
    intros.
    unfold treeseq_pred, tree_rep in *.
    eapply NEforall_d_in'.
    intros.
    destruct H1; simpl in H1.
    eapply NEforall_d_in in H0 as Hx.
    apply Hx.
    rewrite H1; unfold d_in; left; reflexivity.
    destruct H1.
    rewrite <- H1.
    apply H.
    eapply NEforall_d_in in H0 as Hx.
    apply Hx.
    unfold d_in; right; auto.
 Qed.
Lemma treeseq_upd_iter_tree_rep: forall  vsl ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile off,
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) (tsupd_iter ts tmppath off vsl).
(* hint proof tokens: 37 *)
Proof.
  induction vsl; simpl; intros.
  auto.
  apply IHvsl.
  apply treeseq_upd_off_tree_rep; auto.
 Qed.
Definition synced_bdata (data: list byteset):= (map (fun x => (x, nil:list byte)) (map fst data)).
Lemma synced_bdata_length: forall l, length (synced_bdata l) = length l.
(* hint proof tokens: 25 *)
Proof.   
  intros.
  unfold synced_bdata.
  repeat rewrite map_length.
  reflexivity.
Qed.
Lemma bytefile_exists: forall f,
  roundup (# (INODE.ABytes (DFAttr f))) valubytes 
              = Datatypes.length (DFData f) * valubytes ->
  AByteFile.rep f 
      {| ByFData:= firstn (# (INODE.ABytes (DFAttr f)))
                        (concat (map valuset2bytesets (DFData f)));
        ByFAttr := (DFAttr f)|}.
Proof.
(* original proof tokens: 292 *)

(* No more tactics to try *)
Admitted.

Lemma tree_rep_update_subtree: forall ts tf ilist frees Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname  dstfile) ts ->
   tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile
                        {| TStree:= update_subtree tmppath (TreeFile tinum tf) (TStree ts !!);
                            TSilist:= ilist;
                            TSfree:= frees |}.
(* hint proof tokens: 378 *)
Proof.
  intros.
  unfold tree_rep, treeseq_pred in *; simpl.
  eapply NEforall_d_in in H as Hx.
  destruct Hx.
  split.
  eapply tree_names_distinct_update_subtree.
  apply H0.
  apply TND_file.
  destruct H1.
  unfold tree_with_tmp in *; simpl.
  split; eauto.
  destruct H2.
  left.
  exists tf.
  do 2 destruct H2.
  exists x0.
  apply sep_star_comm in H2.
  apply sep_star_assoc in H2.
  eapply dir2flatmem2_update_subtree with (f':= tf) in H2.
  pred_apply; cancel.
  auto.
  right; auto.
  unfold tree_with_src in *; simpl in *.
  destruct H2.
  destruct H2.
  left.
  exists x.
  apply sep_star_comm.
  apply sep_star_assoc.
  apply sep_star_comm in H2.
  apply sep_star_assoc in H2.
  apply dir2flatmem2_find_subtree_ptsto_none in H2 as Hx.
  eapply update_subtree_path_notfound in Hx.
  rewrite Hx.
  pred_apply; cancel.
  all: auto.
  unfold tree_with_dst in *.
  right.
  destruct H2.
  exists x.
  apply sep_star_comm.
  apply sep_star_assoc.
  apply sep_star_comm in H2.
  apply sep_star_assoc in H2.
  apply dir2flatmem2_find_subtree_ptsto_none in H2 as Hx.
  eapply update_subtree_path_notfound in Hx.
  rewrite Hx.
  pred_apply; cancel.
  all: auto.
  apply latest_in_ds.
Qed.
Lemma roundup_div_mul: forall a b,
b<>0 -> roundup a b / b * b = roundup a b.
(* hint proof tokens: 33 *)
Proof.
  intros.
  unfold roundup.
  rewrite mul_div.
  all: auto.
  apply Nat.mod_mul.
  all: lia.
Qed.
Lemma in_not_in_name_eq: forall A (name name': A) (names: list A),
  ~ In name names ->
  In name' names ->
  name <> name'.
Proof.
(* original proof tokens: 59 *)
(* generated proof tokens: 32 *)

intros A name name' names H1 H2.
intro Hneq. subst name'.
apply H1. auto. 
Qed.

Lemma in_add_to_list_or: forall  tree name name' f,
  In name' (map fst (add_to_list name f tree)) ->
  name = name' \/ In name' (map fst tree).
(* hint proof tokens: 87 *)
Proof.
  induction tree; simpl in *; intros; auto.
  destruct a; simpl in *.
  destruct (string_dec s name); simpl in *.
  destruct H.
  left; auto.
  right; right; auto.
  destruct H.
  right; left; auto.
  apply IHtree in H.
  destruct H.
  left; auto.
  right; right; auto.
Qed.
Lemma NoDup_add_to_list: forall tree f fname,
  NoDup (map fst tree) ->
  ~ In fname (map fst tree) ->
  NoDup (map fst (add_to_list fname f tree)).
(* hint proof tokens: 154 *)
Proof.
  induction tree; intros.
  unfold add_to_list.
  apply NoDup_cons.
  apply in_nil.
  apply NoDup_nil.
  destruct a; simpl in *.
  destruct (string_dec s fname); simpl in *.
  destruct H0; left; auto.
  apply NoDup_cons.
  unfold not; intros.
  apply in_add_to_list_or in H1; auto.
  destruct H1.
  apply H0; left; auto.
  apply NoDup_cons_iff in H.
  apply H; auto.
  apply IHtree.
  apply NoDup_cons_iff in H.
  apply H; auto.
  unfold not; intros; apply H0.
  right; auto.
Qed.
Lemma in_add_to_list_tree_or: forall  tree name t t',
  In t (add_to_list name t' tree) ->
  t = (name, t') \/ In t tree.
(* hint proof tokens: 101 *)
Proof.
  induction tree; simpl in *; intros; auto.
  destruct H.
  left; auto.
  right; auto.
  destruct a; simpl in *.
  destruct (string_dec s name); simpl in *.
  destruct H.
  left; auto.
  right; right; auto.
  destruct H.
  right; left; auto.
  apply IHtree in H.
  destruct H.
  left; auto.
  right; right; auto.
Qed.
Hint Extern 1 (Forall (fun sublist : list byteset => Datatypes.length sublist = valubytes)
  (PByFData _)) => eapply proto_len; eauto.
Lemma proto_len_updN: forall f pfy a v,
proto_bytefile_valid f pfy ->
Forall (fun sublist : list byteset => Datatypes.length sublist = valubytes)
  (PByFData pfy) ⟦ a := valuset2bytesets v⟧.
Proof.
(* original proof tokens: 70 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 (Forall (fun sublist : list byteset => Datatypes.length sublist = valubytes)
  (PByFData _) ⟦ _ := valuset2bytesets _⟧) => eapply proto_len_updN; eauto.
Lemma bfile_bytefile_selN_firstn_skipn: forall f fy a b data F def,
AByteFile.rep f fy ->
(F * arrayN (ptsto (V:=byteset)) (a * valubytes + b) data)%pred (list2nmem (ByFData fy)) ->
b + length data <= valubytes ->
firstn (length data) (skipn b (valuset2bytesets (selN (DFData f) a def))) = data.
(* hint proof tokens: 292 *)
Proof.
  intros.
  destruct (length data) eqn:D.
  apply length_zero_iff_nil in D.
  auto.

  apply arrayN_list2nmem in H0 as Hx.
  unfold AByteFile.rep in H; split_hypothesis.
  erewrite <- selN_map.
  rewrite <- H.
  erewrite proto_bytefile_unified_bytefile_selN; eauto.
  unfold get_sublist.
  rewrite <- (skipn_firstn_comm (a*valubytes)).
  rewrite skipn_skipn.
  rewrite <- skipn_firstn_comm.
  rewrite firstn_firstn.
  rewrite min_l.
  erewrite <- unified_bytefile_bytefile_firstn; eauto.
  rewrite skipn_firstn_comm.
  rewrite <- D; rewrite Nat.add_comm; auto.
  apply list2nmem_arrayN_bound in H0 as H'; destruct H';
  try apply length_zero_iff_nil in H7; lia.
  lia.
  erewrite bfile_protobyte_len_eq; eauto.
  eapply inlen_bfile; eauto.
  unfold AByteFile.rep; repeat eexists; eauto.
  lia.
  lia.
  eapply inlen_bfile; eauto.
  unfold AByteFile.rep; repeat eexists; eauto.
  lia.
  lia.
  apply byteset0.
Qed.
Ltac resolve_a_helper:= 
  repeat rewrite app_length;
  repeat rewrite map_length;
  repeat rewrite merge_bs_length; auto;
  repeat rewrite skipn_length;
  repeat rewrite valu2list_len;
  try rewrite firstn_length_l; auto;
  repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto;
  repeat rewrite firstn_length_l; auto;
  try lia;
  try rewrite valu2list_len; try lia.
Ltac resolve_a:= 
    match goal with
      | [ |- _ >= _ ] => resolve_a_helper
      | [ |- _ - _ >= _  ] => resolve_a_helper
      | [ |- _ < _  ] => resolve_a_helper
      | [ |- _ - _ < _  ] => resolve_a_helper
      | [ |- _ - _ - _ < _ ] => resolve_a_helper
      | [ |- _ - _ - _ < _ - _ - _] => resolve_a_helper
    end.
Lemma exists_impl: forall (bsl: @Mem.mem addr addr_eq_dec _) (F: pred) a b_1 b_2,
    (F ✶ (exists old : list byte,
      a |-> (b_1, old) ✶ ⟦⟦ incl (b_1 :: old) (b_1 :: b_2) ⟧⟧))%pred bsl <->
   (exists old, (F ✶ a |-> (b_1, old) ✶ ⟦⟦ incl (b_1 :: old) (b_1 :: b_2) ⟧⟧))%pred bsl.
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Lemma incl_dup_head: forall A (a: A) b c,
    incl (a::b) c -> incl (a::a::b) c.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma dsupd_iter_dsupd_head: forall bnl vsl bn vs ds,
  dsupd_iter (dsupd ds bn vs) bnl vsl = dsupd_iter ds (bn::bnl) (vs::vsl).
Proof.
(* original proof tokens: 13 *)
(* generated proof tokens: 13 *)

simpl. 
reflexivity.
Qed.

Lemma dsupd_iter_dsupd_tail: forall bnl vsl bn vs ds,
  length bnl = length vsl ->
  dsupd (dsupd_iter ds bnl vsl) bn vs = dsupd_iter ds (bnl++[bn]) (vsl++[vs]).
(* hint proof tokens: 72 *)
Proof.
    induction bnl; intros; simpl.
    symmetry in H; apply length_zero_iff_nil in H.
    rewrite H; simpl.
    reflexivity.
    destruct vsl.
    simpl in H; inversion H.
    simpl.
    apply IHbnl.
    simpl in H; inversion H; auto.
  Qed.
Lemma combine_app_tail: forall A B (l1: list A) (l2: list B) e1 e2,
  Datatypes.length l1 = Datatypes.length l2 ->
  combine (l1++[e1]) (l2++[e2]) = (combine l1 l2 ++ [(e1, e2)])%list.
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Lemma map_single: forall A B (f: A -> B) e,
  map f [e] = [f e].
Proof.
(* original proof tokens: 13 *)
(* generated proof tokens: 16 *)

Proof.
  intros. 
  reflexivity.
Qed.

Lemma get_sublist_app_tail: forall A (l: list A) a b def,
  length l >= S (a + b) ->
  get_sublist l a (S b) = (get_sublist l a b ++ [selN l (a+b) def])%list.
(* hint proof tokens: 118 *)
Proof.
    induction l; simpl; intros.
    inversion H.
    unfold get_sublist in *.
    simpl in *.
    destruct a0; simpl.
    destruct b; simpl.
    reflexivity.
    apply le_S_n in H.
    eapply IHl with (a:= 0) in H; simpl in *.
    rewrite H; reflexivity.
    apply le_S_n in H.
    
    eapply IHl with (a:= a0) in H; simpl in *.
    rewrite H.
    auto.
  Qed.
Lemma firstn_eq_nil: forall A n (l: list A),
  firstn n l = nil <-> n = 0 \/ l = nil.
(* hint proof tokens: 58 *)
Proof.
    intros; split; intros.
    destruct l.
    right; reflexivity.
    destruct n.
    left; reflexivity.
    simpl in H; inversion H.
    destruct H; subst; try reflexivity.
    apply firstn_nil.
  Qed.
Lemma skipn_eq_nil: forall A (l: list A)  n ,
  skipn n l = nil <-> n >= length l \/ l = nil.
(* hint proof tokens: 89 *)
Proof.
    induction l; intros; split; intros.
    left; simpl; lia.
    apply skipn_nil.
    destruct n; simpl in *.
    inversion H.
    apply IHl in H.
    destruct H.
    left; lia.
    left; apply length_zero_iff_nil in H; lia.
    destruct H.
    apply skipn_oob; auto.
    inversion H.
  Qed.
Lemma bfile_selN_eq: forall f f' fy fy' F F' a l,
   AByteFile.rep f fy ->
   AByteFile.rep f' fy' ->
   (F ✶ arrayN (ptsto (V:=byteset)) (a * valubytes) l)%pred (list2nmem (ByFData fy)) ->
   (F' ✶ arrayN (ptsto (V:=byteset)) (a * valubytes) l)%pred (list2nmem (ByFData fy')) ->
   length l >= valubytes ->
   selN (DFData f) a valuset0 = selN (DFData f') a valuset0.
(* hint proof tokens: 885 *)
Proof.
    intros.
    apply list2nmem_arrayN_bound in H1 as Hb.
    destruct Hb.
    apply length_zero_iff_nil in H4; pose proof valubytes_ge_O; unfold datatype in *; lia.
    apply list2nmem_arrayN_bound in H2 as Hb'.
    destruct Hb'.
    apply length_zero_iff_nil in H5; pose proof valubytes_ge_O; unfold datatype in *; lia.
    replace (a * valubytes) with (a * valubytes + 0) in H1 by lia.
    eapply inlen_bfile in H1 as Hl; eauto.
    replace (a * valubytes) with (a * valubytes + 0) in H2 by lia.
    eapply inlen_bfile in H2 as Hl'; eauto.
    rewrite <- plus_n_O in *.
    unfold rep in H; split_hypothesis.
    rewrite H7, H6, H in H1.
    apply arrayN_list2nmem in H1 as Hx.
    assert (A: bytesets2valuset (firstn valubytes l) = selN (DFData f) a valuset0).
    rewrite Hx.
    rewrite firstn_firstn.
    rewrite min_l; auto.
    rewrite <- skipn_firstn_comm.
    rewrite firstn_firstn; rewrite min_l.
    rewrite skipn_firstn_comm.
    rewrite concat_hom_skipn with (k:= valubytes).
    rewrite skipn_map_comm.
    replace valubytes with (1 * valubytes) by lia.
    rewrite concat_hom_firstn.
    rewrite firstn_map_comm.
    erewrite firstn_1_selN.
    rewrite skipn_selN.
    rewrite <- plus_n_O.
    simpl.
    rewrite app_nil_r.
    rewrite valuset2bytesets2valuset; eauto.
    {
    unfold not; intros Hn.
    rewrite skipn_eq_nil in Hn.
    destruct Hn.
    unfold datatype in *; lia.
    unfold datatype in *.
    apply length_zero_iff_nil in H11; lia.
    }
    rewrite <- skipn_map_comm.
    rewrite <- H.
    eapply proto_skip_len; eauto.
    rewrite <- H.
    eapply proto_len; eauto.
    lia.
    
    
    unfold rep in H0; split_hypothesis.
    rewrite H12, H11, H0 in H2.
    apply arrayN_list2nmem in H2 as Hx'.
    assert (A': bytesets2valuset (firstn valubytes l) = selN (DFData f') a valuset0).
    rewrite Hx'.
    rewrite firstn_firstn.
    rewrite min_l; auto.
    rewrite <- skipn_firstn_comm.
    rewrite firstn_firstn; rewrite min_l.
    rewrite skipn_firstn_comm.
    rewrite concat_hom_skipn with (k:= valubytes).
    rewrite skipn_map_comm.
    replace valubytes with (1 * valubytes) by lia.
    rewrite concat_hom_firstn.
    rewrite firstn_map_comm.
    erewrite firstn_1_selN.
    rewrite skipn_selN.
    rewrite <- plus_n_O.
    simpl.
    rewrite app_nil_r.
    rewrite valuset2bytesets2valuset; eauto.
    {
    unfold not; intros Hn.
    rewrite skipn_eq_nil in Hn.
    destruct Hn.
    unfold datatype in *; lia.
    unfold datatype in *.
    apply length_zero_iff_nil in H16; lia.
    }
    rewrite <- skipn_map_comm.
    rewrite <- H0.
    eapply proto_skip_len; eauto.
    rewrite <- H0.
    eapply proto_len; eauto.
    lia.
    rewrite <- A; auto.
    apply byteset0.
    apply byteset0.
    apply valubytes_ge_O.
    pose proof valubytes_ge_O; unfold datatype in *; lia.
    apply valubytes_ge_O.
    pose proof valubytes_ge_O; unfold datatype in *; lia.
Qed.
Lemma le_lt_false: forall a b, a <= b -> a > b -> False.
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 17 *)

intros a b Hle Hgt.
lia.
Qed.

Lemma combine_cons: forall A B (a:A) (b:B) c d,
   (a, b)::combine c d = combine (a::c) (b::d).
(* hint proof tokens: 12 *)
Proof. intros; simpl; auto. Qed.
Lemma tsupd_iter_tsupd_head: forall vsl vs ts s pathname,
  tsupd_iter (tsupd ts pathname s vs) pathname (S s) vsl = tsupd_iter ts pathname s (vs::vsl).
Proof.
(* original proof tokens: 13 *)

(* No more tactics to try *)
Admitted.

Lemma tsupd_iter_tsupd_tail: forall vsl s a vs ts pathname,
  a = s + length vsl ->
  tsupd (tsupd_iter ts pathname s vsl) pathname a vs = tsupd_iter ts pathname s (vsl++[vs]).
(* hint proof tokens: 45 *)
Proof.
    induction vsl; intros; simpl in *.
    subst; rewrite <- plus_n_O; auto. 
    rewrite H; simpl.
    apply IHvsl.
    lia.
  Qed.
Lemma dsupd_iter_merge: forall ds bnl data f f' fy fy' block_off bn Fd old_data num_of_full_blocks,
   AByteFile.rep f fy ->
   AByteFile.rep f' fy' ->
   (Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)%pred
  (list2nmem (ByFData fy)) ->
  length old_data = length data ->
  length data = num_of_full_blocks * valubytes ->
  length bnl < num_of_full_blocks ->
  (Fd * arrayN (ptsto (V:=byteset))
     (block_off * valubytes) (merge_bs (firstn (length bnl * valubytes) data) (firstn (length bnl * valubytes) old_data))
 ✶ arrayN (ptsto (V:=byteset))
     ((block_off + Datatypes.length bnl) * valubytes) (skipn (length bnl * valubytes) old_data))%pred
  (list2nmem (ByFData fy')) ->
   (dsupd
        (dsupd_iter ds bnl
           (combine
              (map list2valu
                 (list_split_chunk (Datatypes.length bnl) valubytes
                    (firstn (Datatypes.length bnl * valubytes) data)))
              (map vsmerge
                 (get_sublist (DFData f) block_off (Datatypes.length bnl)))))
        bn
        (list2valu
           (get_sublist data (Datatypes.length bnl * valubytes) valubytes),
        vsmerge (selN (DFData f') (block_off + Datatypes.length bnl) valuset0 ))) = 
        dsupd_iter ds (bnl++[bn])
              (combine
                 (map list2valu
                    (list_split_chunk (S (Datatypes.length bnl)) valubytes
                       (firstn ((S (Datatypes.length bnl)) * valubytes) data)))
                 (map vsmerge (get_sublist (DFData f) block_off (S (Datatypes.length bnl))))).
Proof.
(* original proof tokens: 1216 *)

(* No more tactics to try *)
Admitted.

Lemma tsupd_tsupd_iter_merge: forall ts pathname (bnl: list addr) data f f' fy fy' block_off Fd old_data num_of_full_blocks,
   AByteFile.rep f fy ->
   AByteFile.rep f' fy' ->
   (Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)%pred
  (list2nmem (ByFData fy)) ->
  length old_data = length data ->
  length data = num_of_full_blocks * valubytes ->
  length bnl < num_of_full_blocks ->
  (Fd * arrayN (ptsto (V:=byteset))
     (block_off * valubytes) (merge_bs (firstn (length bnl * valubytes) data) (firstn (length bnl * valubytes) old_data))
 ✶ arrayN (ptsto (V:=byteset))
     ((block_off + Datatypes.length bnl) * valubytes) (skipn (length bnl * valubytes) old_data))%pred
  (list2nmem (ByFData fy')) ->
   (tsupd
        (tsupd_iter ts pathname block_off
           (combine
              (map list2valu
                 (list_split_chunk (Datatypes.length bnl) valubytes
                    (firstn (Datatypes.length bnl * valubytes) data)))
              (map vsmerge
                 (get_sublist (DFData f) block_off (Datatypes.length bnl)))))
        pathname (block_off + Datatypes.length bnl)
        (list2valu
           (get_sublist data (Datatypes.length bnl * valubytes) valubytes),
        vsmerge (selN (DFData f') (block_off + Datatypes.length bnl) valuset0 ))) = 
        tsupd_iter ts pathname block_off
              (combine
                 (map list2valu
                    (list_split_chunk (S (Datatypes.length bnl)) valubytes
                       (firstn ((S (Datatypes.length bnl)) * valubytes) data)))
                 (map vsmerge (get_sublist (DFData f) block_off (S (Datatypes.length bnl))))).
(* hint proof tokens: 1247 *)
Proof.
      intros.
      rewrite tsupd_iter_tsupd_tail.
      rewrite <- combine_app_tail with (e1:= list2valu
       (get_sublist data (Datatypes.length bnl * valubytes) valubytes))
       (e2:= vsmerge (DFData f') ⟦ block_off + Datatypes.length bnl ⟧).
      rewrite <- map_single.
      rewrite <- map_single with (f:= vsmerge).
      repeat rewrite <- map_app.
       
       erewrite bfile_selN_eq.
       rewrite <- get_sublist_app_tail.
       rewrite <- list_split_chunk_app_1.
       unfold get_sublist.
       rewrite <- firstn_sum_split.
       destruct (map vsmerge
          (firstn (S (Datatypes.length bnl)) (skipn block_off (DFData f)))) eqn:D.
       apply map_eq_nil in D; apply firstn_eq_nil in D.
       destruct D.
       inversion H6.
       apply skipn_eq_nil in H6.
       destruct H6.
       
       assert (block_off < Datatypes.length (DFData f)).
       eapply inlen_bfile with (j:= 0); try rewrite <- plus_n_O; eauto.
       rewrite valubytes_is; lia.
       rewrite H2; rewrite H3; rewrite valubytes_is; lia.
       
       apply le_lt_false in H6; auto.
       inversion H6.
       
       assert (block_off < Datatypes.length (DFData f)).
       eapply inlen_bfile with (j:= 0); try rewrite <- plus_n_O; eauto.
       rewrite valubytes_is; lia.
       rewrite H2; rewrite H3; rewrite valubytes_is; lia.
       
       rewrite H6 in H7; simpl in H7; inversion H7.

       replace ((Datatypes.length bnl * valubytes + valubytes))
          with (S (Datatypes.length bnl) * valubytes) by (simpl; lia).
          replace (Datatypes.length bnl + 1) with (S (Datatypes.length bnl)) by lia.
       rewrite <- D; eauto.
       
       rewrite firstn_length_l. lia.
       rewrite H3; rewrite valubytes_is; lia.
       apply firstn_length_l.
       rewrite skipn_length;
       apply Nat.le_add_le_sub_l; simpl.
       rewrite H3; rewrite valubytes_is; lia.
       
       
       apply lt_le_S.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.le_add_le_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; lia.
       eauto.
       eauto.
       eauto.
       
       pred_apply.
       rewrite arrayN_split with (i:= length bnl * valubytes).
       rewrite Nat.mul_add_distr_r; cancel.
       rewrite skipn_length.
       apply Nat.le_add_le_sub_l; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; lia.
       repeat rewrite map_length.
       rewrite list_split_chunk_length.
       rewrite get_sublist_length.
       apply min_l.
       rewrite firstn_length_l.
       rewrite Nat.div_mul; auto.
       rewrite H3;  rewrite valubytes_is; lia.
       
       apply Nat.lt_le_incl.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.lt_add_lt_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; lia.
       auto.
       
       apply firstn_length_l.
       rewrite H3; rewrite valubytes_is; lia.
        apply Nat.add_cancel_l.
       unfold datatype.
       rewrite combine_length.
       rewrite min_r.
       rewrite map_length; rewrite get_sublist_length; auto.
       
       apply Nat.lt_le_incl.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.lt_add_lt_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; lia.
       auto.
       
       repeat rewrite map_length.
       rewrite list_split_chunk_length.
       rewrite get_sublist_length.
       rewrite min_l; auto.
       rewrite firstn_length_l.
       rewrite Nat.div_mul; auto.
       rewrite H3;  rewrite valubytes_is; lia.
       apply Nat.lt_le_incl.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.lt_add_lt_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; lia.
       auto.
       
       apply firstn_length_l.
       rewrite H3; rewrite valubytes_is; lia.
   Qed.
Lemma arrayN_merge_bs_split_firstn: forall l l' a b c,
    arrayN (ptsto (V:=byteset)) a (merge_bs (firstn b l) (firstn b l')) *
    arrayN (ptsto (V:=byteset)) (a + b) 
        (merge_bs (firstn c (skipn b l)) (firstn c (skipn b l'))) <=p=>
    arrayN (ptsto (V:=byteset)) a (merge_bs (firstn (b + c) l) (firstn (b + c) l')).
Proof.
(* original proof tokens: 137 *)

(* No more tactics to try *)
Admitted.

Lemma diskIs_ptsto_updN: forall {V} (l l': list V) a v,
(diskIs (mem_except (list2nmem l) a) * a |-> v)%pred (list2nmem l') ->
a < length l ->
l' = updN l a v.
Proof.
(* original proof tokens: 47 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_arrayN_app_iff_general:
  forall (A : Type) (F : pred) (l l' : list A) a,
  a = length l ->
  (F ✶ arrayN (ptsto (V:=A)) a l')%pred (list2nmem (l ++ l')) ->
  F (list2nmem l).
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Lemma proto_bytefile_bytefile_arrayN_app_end_eq: forall a l f pfy ufy fy F,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
(F * arrayN (ptsto (V:=byteset)) (a * valubytes) l)%pred (list2nmem (ByFData fy)) ->
length l = length (ByFData fy) - a * valubytes ->
l <> nil ->
(ByFData fy) = (concat (firstn a (PByFData pfy)) ++ l)%list.
(* hint proof tokens: 142 *)
Proof.
  intros.
  apply arrayN_list2nmem in H2 as Hx.
  rewrite firstn_oob in Hx.
  rewrite Hx.
  rewrite <- concat_hom_firstn with (k:= valubytes).
  rewrite <- H0.
  erewrite <- unified_bytefile_bytefile_firstn; eauto.
  rewrite firstn_skipn; auto.
  apply list2nmem_arrayN_bound in H2.
  destruct H2.
  subst; simpl in *.
  destruct H4; auto.
  lia.
  eapply proto_len; eauto.
  rewrite skipn_length; lia.
  apply byteset0.
Qed.
Lemma fold_valuset2bytesets: forall f block_off,
(map (list2byteset byte0)
     (valuset2bytesets_rec
        (valu2list (fst (selN (DFData f) block_off valuset0))
         :: map valu2list (snd (selN (DFData f) block_off valuset0))) valubytes)) = valuset2bytesets (selN (DFData f) block_off valuset0).
(* hint proof tokens: 9 *)
Proof. reflexivity. Qed.
Lemma ppmmm_1_5_cancel: forall a b c d e,
a + b + c - d - a - e = b + c - d - e.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma list2nmem_arrayN_bound_nonnil: forall V (l: list V) a F l',
l <> nil ->
(F * arrayN (ptsto(V:= V)) a l)%pred (list2nmem l') ->
a + length l <= length l'.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma sep_star_modified_bytefile: forall f pfy ufy fy Fd block_off head_data old_data tail_data data, 
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
ByFAttr fy = DFAttr f ->
# (INODE.ABytes (ByFAttr fy)) = length (ByFData fy) ->
roundup (length (ByFData fy)) valubytes = length (DFData f) * valubytes ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) (head_data ++ old_data++tail_data))%pred (list2nmem (ByFData fy)) ->
length old_data = length data ->
length data > 0 ->
length head_data + length data <= valubytes ->
Init.Nat.min
       (length (ByFData fy) -
        (block_off * valubytes + length head_data + length data))
       (valubytes - (length head_data + length data)) = length tail_data ->
       
(((Fd
   ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes)
       (merge_bs (map fst head_data) head_data))
  ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes + length head_data)
      (merge_bs data old_data))
 ✶ arrayN (ptsto (V:=byteset))
     (block_off * valubytes + length head_data + length data)
     (merge_bs (map fst tail_data) tail_data))%pred
  (list2nmem
     (ByFData
        {|
        ByFData := firstn (length (ByFData fy))
                     (concat
                        (PByFData pfy) ⟦ block_off
                        := valuset2bytesets
                             (list2valu
                                (firstn (length head_data)
                                   (valu2list (fst (selN (DFData f) block_off valuset0 ))) ++
                                 data ++
                                 skipn (length head_data + length data)
                                   (valu2list (fst (selN (DFData f) block_off valuset0 )))),
                             vsmerge (selN (DFData f) block_off valuset0 )) ⟧);
        ByFAttr := ByFAttr fy |})).
(* hint proof tokens: 2643 *)
Proof.
  intros.
  assert (A: (head_data ++ old_data ++ tail_data)%list <> []).
  unfold not; intros H';
  apply length_zero_iff_nil in H';
  repeat rewrite app_length in H'; lia.
  
  assert (A0: block_off <= length (PByFData pfy)).
  eapply block_off_le_length_proto_bytefile with (byte_off:= 0); 
  try rewrite <- plus_n_O; eauto; try lia; length_rewrite_l.
  
  apply list2nmem_arrayN_bound_nonnil in H5 as A1; 
  repeat rewrite app_length in A1; auto; try lia.
  
apply sep_star_assoc.
rewrite <- arrayN_app'; [| length_rewrite_l; auto].
apply sep_star_assoc.
rewrite <- arrayN_app'; [| length_rewrite_l; auto].
repeat rewrite <- merge_bs_app; [| length_rewrite_l; auto | length_rewrite_l; auto].

simpl.
unfold valuset2bytesets; simpl.
rewrite list2valu2list; [| length_rewrite_l; auto].
rewrite valuset2bytesets_rec_cons_merge_bs.
rewrite updN_firstn_skipn.
rewrite concat_app; simpl.
rewrite firstn_app_le; [ | length_rewrite_l; auto; eapply proto_len_firstn; eauto].
length_rewrite_l; [ | eapply proto_len_firstn; eauto].

destruct (le_dec (length (ByFData fy) - (block_off * valubytes + length head_data + length data))
       (valubytes - (length head_data + length data))).
       

rewrite min_l in H9; try lia.
rewrite firstn_app_l; [| length_rewrite_l; auto].
rewrite merge_bs_firstn_comm.
rewrite firstn_app_le; [| length_rewrite_l; auto].
rewrite firstn_length_l; [| length_rewrite_l; auto].
rewrite firstn_app_le; [| length_rewrite_l; auto].

replace (firstn (length head_data) (valu2list (fst (DFData f) ⟦ block_off ⟧)))
  with (map fst head_data).
  
replace (firstn
           (length (ByFData fy) - block_off * valubytes - length head_data -
            length data)
           (skipn (length head_data + length data)
              (valu2list (fst (DFData f) ⟦ block_off ⟧))))
  with (map fst tail_data).
rewrite fold_valuset2bytesets.
replace (firstn (length (ByFData fy) - block_off * valubytes)
          (valuset2bytesets (DFData f) ⟦ block_off ⟧))
with (head_data ++ old_data ++ tail_data)%list.
apply list2nmem_arrayN_app_general;  [| length_rewrite_l; auto; [eapply proto_len_firstn; eauto] | auto ].

eapply list2nmem_arrayN_app_iff_general.
2: erewrite <- proto_bytefile_bytefile_arrayN_app_end_eq; eauto; length_rewrite_l; auto.

length_rewrite_l; eapply proto_len_firstn; eauto.

replace (length (ByFData fy) - block_off * valubytes)
  with (length (head_data ++ old_data ++ tail_data)%list); [| length_rewrite_l].

replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0))) by auto.
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[ unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; eauto |
  length_rewrite_l; eauto].

rewrite <- mapfst_valuset2bytesets.
replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0))) by auto.
rewrite <- skipn_firstn_comm.
replace (length head_data + length data +
      (length (ByFData fy) - block_off * valubytes - length head_data -
       length data))
with (length (ByFData fy) - block_off * valubytes); [ | subst; lia].
rewrite firstn_map_comm.
replace (length (ByFData fy) - block_off * valubytes)
  with (length (head_data ++ old_data ++ tail_data)); [| length_rewrite_l; auto].
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[ | unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; eauto |
  length_rewrite_l; eauto].
rewrite skipn_map_comm.
rewrite <- H6.
rewrite <- app_length.
rewrite app_assoc.
rewrite skipn_app; auto.

rewrite <- mapfst_valuset2bytesets.
replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0))) by auto.
rewrite firstn_map_comm.

rewrite arrayN_app in H5.
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[ unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; pred_apply; cancel |
  length_rewrite_l; eauto].



rewrite min_r in H9; try lia.

assert (A2: block_off + 1 <= length (PByFData pfy)).
apply le_mult_weaken with (p:= valubytes); eauto.
erewrite <- unified_byte_protobyte_len; eauto.
eapply le_trans.
2: eapply bytefile_unified_byte_len; eauto.
rewrite Nat.mul_add_distr_r; simpl; lia.

rewrite firstn_app_le; [ length_rewrite_l; auto | length_rewrite_l; auto].
replace (length (ByFData fy) - block_off * valubytes -
         (length head_data +
          (length data + (valubytes - (length head_data + length data)))))
with (length (ByFData fy) - block_off * valubytes - valubytes) by lia.

replace (firstn (length head_data) (valu2list (fst (DFData f) ⟦ block_off ⟧)))
  with (map fst head_data).
  
replace (skipn (length head_data + length data)
              (valu2list (fst (DFData f) ⟦ block_off ⟧)))
  with (map fst tail_data).
rewrite fold_valuset2bytesets.
replace (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (head_data ++ old_data ++ tail_data)%list.
apply list2nmem_arrayN_middle with (b:= valubytes);  [length_rewrite_l; auto; eapply proto_len_firstn; eauto | length_rewrite_l; auto | auto].

apply arrayN_frame_mem_ex_range in H5 as Hx; repeat rewrite app_length in Hx.


erewrite mem_except_range_out_apply with (l2':= (head_data ++ old_data ++ tail_data)%list); length_rewrite_l; auto; [| eapply proto_len_firstn; eauto]; repeat rewrite <- plus_n_O.

replace (head_data ++ old_data ++ tail_data)%list with (concat (firstn 1 (skipn block_off (PByFData pfy)))).

rewrite app_assoc.
rewrite <- concat_app.
rewrite <- firstn_sum_split.

replace (length (ByFData fy) - block_off * valubytes - valubytes)
with (length (ByFData fy) - length (concat (firstn (block_off + 1) (PByFData pfy))));
[| length_rewrite_l; eapply proto_len_firstn; eauto ].

rewrite <- firstn_app_le; [| length_rewrite_l; eapply proto_len_firstn; eauto ].

rewrite <- concat_app.

replace (firstn (block_off + 1) (PByFData pfy) ++
          skipn (block_off + 1) (PByFData pfy))%list
with (PByFData pfy) by (symmetry; apply firstn_skipn).
rewrite <- H0.
rewrite <- H1.

replace (length head_data + (length old_data + length tail_data))
  with valubytes in Hx; [auto | lia].

rewrite firstn_1_selN with (def:= nil).
rewrite skipn_selN; rewrite <- plus_n_O.
simpl; rewrite app_nil_r.
erewrite proto_bytefile_unified_bytefile_selN; eauto.
unfold get_sublist.
rewrite <- skipn_firstn_comm.
erewrite <- unified_bytefile_bytefile_firstn; eauto; try lia.
rewrite skipn_firstn_comm.

eapply arrayN_list2nmem in H5; eauto.
replace (length (head_data ++ old_data ++ tail_data)%list) with valubytes in H5; auto; length_rewrite_l.
apply byteset0.
lia.

unfold not; intros Hy.
apply skipn_eq_nil in Hy.
destruct Hy.
lia.
apply length_zero_iff_nil in H10; lia.

replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (firstn (length (head_data ++ old_data ++ tail_data)%list)(skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0)))).
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[ unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; eauto |
  length_rewrite_l; eauto].
  simpl; apply firstn_oob; length_rewrite_l; lia.
  

rewrite <- mapfst_valuset2bytesets.
replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (firstn (length (head_data ++ old_data ++ tail_data)%list)(skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0))));
[| simpl; apply firstn_oob; length_rewrite_l; lia].
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[ rewrite skipn_map_comm;
  rewrite <- H6;
  rewrite <- app_length;
  rewrite app_assoc;
  rewrite skipn_app; auto  | 
  unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; eauto |
  length_rewrite_l; eauto].
  

rewrite <- mapfst_valuset2bytesets.

replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (firstn (length (head_data ++ old_data ++ tail_data)%list)(skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0))));
[| simpl; apply firstn_oob; length_rewrite_l; lia].
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[  | 
  unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; eauto |
  length_rewrite_l; eauto].
  
  rewrite map_app; rewrite firstn_app_l; 
  [ symmetry; apply firstn_oob; length_rewrite_l; auto 
    |length_rewrite_l; auto].


apply lt_mult_weaken with (p:= valubytes); eauto.
erewrite <- unified_byte_protobyte_len; eauto.
eapply lt_le_trans.
2: eapply bytefile_unified_byte_len; eauto.
lia.

apply Forall_cons.
length_rewrite_l; auto.
apply valu2list_sublist_v.
Qed.
Lemma map_app_tail: forall A B (f: A -> B) (l: list A) e,
    (map f l ++ [f e])%list = map f (l ++ [e])%list.
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_tsupd_updN: forall Ftree pathname inum f f' ts block_off v,
        tree_names_distinct (TStree ts !!) ->
        (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
        (Ftree ✶ pathname |-> File inum f')%pred
        (dir2flatmem2 (TStree (tsupd ts pathname block_off v) !!)) ->
        DFData f' = updN (DFData f) block_off v.
(* hint proof tokens: 124 *)
Proof.
          intros.
          rewrite tsupd_latest in H1.
          rewrite treeseq_one_upd_alternative in H1.
          apply dir2flatmem2_find_subtree_ptsto in H0 as Hy; auto.
          rewrite Hy in H1; simpl in *.
          apply dir2flatmem2_find_subtree_ptsto in H1 as Hz; auto.
          erewrite find_update_subtree in Hz; eauto.
          inversion Hz.
          simpl; auto.
          apply tree_names_distinct_update_subtree; auto.
          apply TND_file.
        Qed.
Lemma tree_names_distinct_treeseq_one_upd': forall t tmppath off vs,
        tree_names_distinct (TStree t) ->
        tree_names_distinct (TStree (treeseq_one_upd t tmppath off vs)).
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_tsupd: forall t tmppath off vs,
        tree_names_distinct (TStree t !!) ->
        tree_names_distinct (TStree (tsupd t tmppath off vs) !!).
(* hint proof tokens: 32 *)
Proof.
          intros.
          rewrite tsupd_latest.
          apply tree_names_distinct_treeseq_one_upd'; auto.
        Qed.
Lemma bfile_selN_tsupd_iter_eq: forall l Ftree pathname inum f f' ts block_off a,
    tree_names_distinct (TStree ts !!) ->
    (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
    (Ftree ✶ pathname |-> File inum f')%pred
        (dir2flatmem2
           (TStree
              (tsupd_iter ts pathname block_off l) !!)) ->
        length l <= a ->
      selN (DFData f) (block_off + a) valuset0 =
      selN (DFData f') (block_off + a) valuset0.
Proof.
(* original proof tokens: 281 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_tsupd_iter:forall l ts pathname off,
        tree_names_distinct (TStree ts !!) ->
        tree_names_distinct
        (TStree
        (tsupd_iter ts pathname off l) !!).
(* hint proof tokens: 36 *)
Proof.
          induction l; intros.
          auto.
          simpl.
          apply IHl.
          apply tree_names_distinct_tsupd; auto.
        Qed.
Lemma roundup_div_S_eq: forall a b,
        b <> 0 ->
        a mod b > 0 ->
        roundup a b / b = S (a / b).
(* hint proof tokens: 50 *)
Proof.
          intros.
          rewrite roundup_eq; auto; [| lia].
          rewrite <- divmult_plusminus_eq; auto.
          rewrite Nat.div_add; auto.
          rewrite Nat.div_same; auto; lia.
        Qed.
Lemma roundup_eq_mod_O: forall a b,
        b <> 0 ->
        a mod b = 0 ->
        roundup a b = a.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma inlen_bfile_S: forall f fy l block_off Fd,
        AByteFile.rep f fy ->
        (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes)
              l )%pred (list2nmem (ByFData fy)) ->
        length l > 0 ->
        S block_off <= length (DFData f).
Proof.
(* original proof tokens: 119 *)

(* No more tactics to try *)
Admitted.

Lemma min_eq_O: forall a b,
        min a b = 0 -> a = 0 \/ b = 0.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma tsupd_tsupd_iter_merge': forall ts pathname data f fy 
        block_off Fd old_data tail_data,
   AByteFile.rep f fy ->
    ((Fd
       ✶ (arrayN (ptsto (V:=byteset)) (block_off * valubytes)
            (firstn (length data / valubytes * valubytes) old_data)
          ✶ arrayN (ptsto (V:=byteset))
              ((block_off + length data / valubytes) * valubytes)
              (skipn (length data / valubytes * valubytes) old_data)))
      ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length old_data) tail_data)%pred
       (list2nmem (ByFData fy)) ->
  length old_data = length data ->
  0 < length (skipn (length data / valubytes * valubytes) data) ->
  min (length (ByFData fy) - (block_off * valubytes + length data))
       (hpad_length (length data)) = length tail_data ->
   tsupd
  (tsupd_iter ts pathname block_off
     (combine
        (map list2valu
           (list_split_chunk (length data / valubytes) valubytes
              (firstn (length data / valubytes * valubytes) data)))
        (map vsmerge
           (get_sublist (DFData f) block_off
              (length data / valubytes))))) pathname
  (block_off + length data / valubytes)
  (list2valu
     (skipn (length data / valubytes * valubytes) data ++
      skipn
        (length (skipn (length data / valubytes * valubytes) data))
        (valu2list
           (fst (selN (DFData f) (block_off + length data / valubytes) valuset0)))),
  vsmerge (selN (DFData f) (block_off + length data / valubytes) valuset0)) =
tsupd_iter ts pathname block_off
  (combine
     (map list2valu
        (list_split_chunk
           (roundup (length data) valubytes / valubytes) valubytes
           (data ++
            skipn (length data mod valubytes)
              (valu2list
                 (fst (selN (DFData f) (block_off + length data / valubytes) valuset0))))))
     (map vsmerge
        (firstn (roundup (length data) valubytes / valubytes)
           (skipn block_off (DFData f))))).
Proof.
(* original proof tokens: 725 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_mod_0: forall a b,
    b <> 0 -> roundup a b mod b = 0.
(* hint proof tokens: 21 *)
Proof.
      intros; unfold roundup.
      apply Nat.mod_mul; auto.
    Qed.
Lemma list_split_chunk_app_l: forall {A} a  b (l1 l2: list A),
   length l1 >= a * b ->
   list_split_chunk a b (l1++l2) = list_split_chunk a b l1.
(* hint proof tokens: 102 *)
Proof.
      induction a; intros.
      simpl in *.
      auto.
      simpl.
      rewrite firstn_app_l.
      rewrite skipn_app_l.
      rewrite IHa; auto.
      simpl in *.
      rewrite skipn_length.
      lia.
      simpl in *.
      eapply le_trans.
      2: eauto.
      apply le_plus_l.
      eapply le_trans.
      2: eauto.
      apply le_plus_l.
    Qed.
Lemma mod_lt_nonzero: forall a b,
   b <> 0 -> a > 0 -> a < b -> a mod b <> 0.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_lt_one: forall a b,
  b <> 0 -> a > 0 -> a <= b -> roundup a b = b.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Lemma le_sub_le_add_l': forall a b c,
    a > 0 -> a <= b - c -> c + a <= b.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma le_sub_le_add_r': forall a b c,
    a > 0 -> a <= b - c -> a + c <= b.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma lt_sub_lt_add_l': forall a b c,
    a < b - c -> c + a < b.
Proof.
(* original proof tokens: 10 *)

(* No more tactics to try *)
Admitted.

Lemma lt_sub_lt_add_r': forall a b c,
    a < b - c -> a + c < b.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma mm_dist': forall a b c,
  b >= c -> a - (b - c) = a + c - b.
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 11 *)

intros; lia.
Qed.

Lemma bytefile_length_eq: forall f f' fy fy',
  AByteFile.rep f fy ->
  AByteFile.rep f' fy' ->
  ByFAttr fy = ByFAttr fy' ->
  length (ByFData fy) = length (ByFData fy').
(* hint proof tokens: 36 *)
Proof.
    intros.
    unfold AByteFile.rep in *; split_hypothesis.
    rewrite <- H10; rewrite H1; auto.
  Qed.
Lemma roundup_div_minus_S: forall a b,
  b<>0 -> a >= b -> S (roundup (a - b) b / b) = roundup a b / b.
(* hint proof tokens: 75 *)
Proof.
    intros.
    unfold roundup.
    repeat rewrite Nat.div_mul; auto.
    rewrite divup_sub_1; auto; try lia.
    destruct (divup a b) eqn:D.
    assert (divup a b > 0).
    apply divup_gt_0; lia.
    lia.
    lia.
  Qed.
Lemma list_split_chunk_cons': forall A a b (l l': list A),
  length l = b ->
  l :: list_split_chunk a b l' = list_split_chunk (S a) b (l ++ l').
(* hint proof tokens: 65 *)
Proof.
      intros.
      simpl.
      rewrite firstn_app_l; try lia.
      rewrite skipn_app_r_ge; try lia.
      rewrite H; replace (b - b) with 0 by lia; simpl; auto.
      rewrite firstn_oob; auto; lia.
  Qed.
Lemma app_assoc_middle_2': forall A (l1 l2 l3 l4: list A),
  (l1 ++ l2 ++ l3 ++ l4)%list =  (l1 ++ (l2 ++ l3) ++ l4)%list.
Proof.
(* original proof tokens: 15 *)
induction l1; simpl; auto.
induction l2; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma skipn_updN_oob_eq :
forall (A : Type) (l : list A) (i n : addr) (v : A),
n > i -> skipn n (l ⟦ i := v ⟧) = skipn n l.
Proof.
(* original proof tokens: 105 *)
unfold skipn; destruct l; simpl; intros; auto.
(* No more tactics to try *)
Admitted.

Lemma roundup_div_minus:
  forall a b : addr,
  b <> 0 -> a >= b -> roundup (a - b) b / b = roundup a b / b - 1.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma list_split_chunk_firstn_cancel: forall A a b (l: list A),
  list_split_chunk a b (firstn (a * b) l) = list_split_chunk a b l.
Proof.
(* original proof tokens: 48 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_pred_tree_rep_latest: forall Ftree srcpath tmppath srcinum file tinum dstbase dstname
           dstfile ts,  
  treeseq_pred
        (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname
           dstfile) ts ->
  tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile
  ts !!.
Proof.
(* original proof tokens: 54 *)

(* No more tactics to try *)
Admitted.

