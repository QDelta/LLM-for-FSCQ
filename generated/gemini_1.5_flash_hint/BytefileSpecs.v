Require Import String.
Require Import Hashmap.
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
Require Import BACHelper.
Require Import AtomicCp.
Import DIRTREE.
Import DTCrash.
Import TREESEQ.
Import ATOMICCP.
Import ListNotations.
Set Implicit Arguments.
Notation tree_rep := ATOMICCP.tree_rep.
Notation rep := AByteFile.rep.
Hint Resolve valubytes_ne_O.
Hint Resolve valubytes_ge_O.
Ltac proto_bytefile_rewrite:=
  match goal with
  | [H: proto_bytefile_valid _ ?pfy |- context[PByFData ?pfy] ] => rewrite H
  end.
Ltac solve_rep:= unfold AByteFile.rep; repeat eexists; eauto.
Ltac nlt_eq_0:=
  match goal with
   | [H: 0 < _ -> False |- _ ] => 
                apply Nat.nlt_ge in H; inversion H as [Hx | ]
   end.
Ltac rewrite_0:= 
   match goal with
   | [H: _ = 0 |- _ ] => try rewrite H; simpl; try rewrite <- plus_n_O
   end.
Ltac rewrite_nlt :=
   match goal with
   | [H: 0 < _ -> False |- _ ] => nlt_eq_0; rewrite_0
   end.
Ltac xcrash_dwrite_to_block x0:= 
    match goal with | [H: (_, _) = _, H0: treeseq_in_ds _ _ _ _ (_, _) _ |- _ ] => 
          rewrite H in H0 end;
    match goal with | [H: MSAlloc ?a = _, H0: _ = MSAlloc ?a |- _ ] => 
          rewrite H in H0; clear H end;
    cancel;
    do 2 (rewrite crash_xform_exists_comm; cancel);
    rewrite crash_xform_exists_comm; unfold pimpl; intros;
    exists x0;
    pred_apply;
    repeat (rewrite crash_xform_sep_star_dist;
       rewrite crash_xform_lift_empty);
    safecancel;
    eauto.
Ltac solve_ineq_dwrite_middle := 
    length_rewrite_l; auto;
    repeat match goal with | [H: ?a = _ |- context[?a] ] =>  rewrite H end;
    try apply Nat.le_add_le_sub_l;
    try rewrite <- Nat.mul_succ_l;
    try apply mult_le_compat_r;
    lia.
Ltac solve_dsupd_iter:=
    rewrite skipn_oob; [| solve_ineq_dwrite_middle];
    rewrite app_nil_r;
    eapply dsupd_iter_merge; eauto.
Ltac solve_tsupd_iter:=
    rewrite skipn_oob;  [| solve_ineq_dwrite_middle];
    rewrite app_nil_r;
    eapply tsupd_tsupd_iter_merge; eauto.
Ltac solve_cancel_dwrite_middle block_off bnl :=
     rewrite <- plus_n_O;
     repeat rewrite Nat.mul_add_distr_r; simpl; 
     repeat rewrite Nat.add_assoc;
     rewrite skipn_skipn;
     replace (block_off * valubytes + valubytes + length bnl * valubytes)
      with  (block_off * valubytes + length bnl * valubytes + valubytes) by lia;
      cancel;
      rewrite sep_star_comm;
      unfold get_sublist;
      replace (valubytes + length bnl * valubytes)
        with(length bnl * valubytes + valubytes) by lia;
      rewrite arrayN_merge_bs_split_firstn; cancel.
Lemma div_mod': forall x y,
    y <> 0 -> x / y * y + x mod y = x.
(* hint proof tokens: 25 *)
Proof.
    intros.
    rewrite Nat.mul_comm;
    rewrite <- Nat.div_mod; auto.
  Qed.
Lemma mod_eq': forall a b,
    b <> 0 ->
    a - a / b * b = a mod b.
(* hint proof tokens: 26 *)
Proof.
    intros;
    rewrite Nat.mul_comm; 
    rewrite <- Nat.mod_eq; auto.
  Qed.
Ltac solve_length_le_v:=
     length_rewrite_l;
     rewrite mod_eq'; auto;
    apply Nat.mod_upper_bound; auto.
Ltac solve_length_le:=
    rewrite Nat.mul_comm; try match goal with | [H: length _ = length _ |- _ ] => rewrite H end; 
    apply Nat.mul_div_le; auto;
    solve_length_le_v.
Ltac simpl_skipn_lt:=
      match goal with | [H: 0 < length (skipn _ _) |- _] =>
      rewrite skipn_length in H; rewrite Nat.mul_comm in H;
      rewrite <- Nat.mod_eq in H; auto end.
Ltac unfold_rep:= 
    repeat match goal with | [H: rep _ _ |- _] => unfold AByteFile.rep in H end;
    split_hypothesis; auto.
Ltac solve_min_dwrite_middle fy fy' data:=
    replace (length (ByFData fy')) with (length (ByFData fy));
    [ simpl_skipn_lt;
      match goal with | [H: min _ _ = _ |- _] => unfold hpad_length in H; simpl in * end;
      length_rewrite_l; repeat rewrite mod_eq'; auto;
      rewrite Nat.mul_add_distr_r; 
      rewrite <- Nat.add_assoc; rewrite div_mod'; auto;
      destruct (length data mod valubytes); lia | eapply bytefile_length_eq; eauto ].
Ltac solve_cancel_dwrite_middle2:=
    pred_apply; repeat rewrite Nat.mul_add_distr_r;
    length_rewrite_l; rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; eauto;
    [ cancel; rewrite sep_star_comm;
      rewrite <- arrayN_app';  
      [ rewrite <- merge_bs_app; repeat rewrite firstn_skipn; eauto | ];
   length_rewrite_l; solve_length_le | length_rewrite_l; solve_length_le ].
Ltac solve_eq_dwrite_middle:= 
      length_rewrite_l; auto;
      try rewrite Nat.div_mul; auto; 
      try solve_length_le; auto.
Lemma tree_with_src_the_dnum: forall Fm Ftop fsxp mscs Ftree srcpath tmppath srcinum file
      dstbase dstname dstfile ts ds sm,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile%pred
          (dir2flatmem2 (TStree ts !!)) ->
    exists direlem, 
        find_subtree [] (TStree ts !!) = Some (TreeDir the_dnum direlem).
(* hint proof tokens: 130 *)
Proof.
    intros.
    unfold tree_with_src in H0.
    edestruct dir2flatmem2_find_subtree_ptsto_dir with 
      (tree := TStree ts !!) (fnlist := @nil string)
      (F := (exists dstinum : addr,
          (Ftree ✶ (srcpath |-> File srcinum file)
           ✶ tmppath |-> Nothing)
          ✶ (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred).
    distinct_names'.
    pred_apply; cancel.
    eexists x; auto.
  Qed.
Lemma crash_ts_split: forall dummy1 dummy5 temp_fn srcinum dummy6 dummy4 dstbase
           dstname dummy9 dummy3 dummy dummy0 fsxp mscs dummy2 sm,
  treeseq_pred
        (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
           dstname dummy9) dummy3 ->
  treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ->
  emp
⇨⇨ crash_xform
     (exists t : treeseq_one,
        (⟦⟦ dummy3 = (t, []) ⟧⟧
         ✶ ⟦⟦ treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ⟧⟧)
        ✶ ⟦⟦ treeseq_pred
               (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
                  dstname dummy9) dummy3 ⟧⟧)
   ⋁ crash_xform
       (exists
          (t : treeseq_one) (ts'' : nelist treeseq_one) (dfile : dirfile),
          ((⟦⟦ dummy3 = pushd t ts'' ⟧⟧
            ✶ ⟦⟦ treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ⟧⟧)
           ✶ ⟦⟦ tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
                  dstname dfile t ⟧⟧)
          ✶ ⟦⟦ treeseq_pred
                 (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
                    dstname dummy9) ts'' ⟧⟧).
(* hint proof tokens: 106 *)
Proof.
    intros.
    destruct dummy3.
    destruct l.
    or_l; xcrash; eauto.
    or_r; xcrash.
    instantiate (1:= (t, l)).
    instantiate (1:= t0).
    simpl; auto.
    inversion H; simpl in *;
    inversion H2; eauto.
    split; simpl.
    inversion H; simpl; auto.
    inversion H; simpl in *;
    inversion H2; eauto.
  Qed.
Lemma crash_ts_split': forall dummy1 dummy5 temp_fn srcinum dummy6 dummy4 dstbase
           dstname dummy9 dummy3 dummy dummy0 fsxp mscs dummy2 sm,
  treeseq_pred
        (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
           dstname dummy9) dummy3 ->
  treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ->
  emp
⇨⇨ crash_xform
     (exists t : treeseq_one,
        (⟦⟦ dummy3 = (t, []) ⟧⟧
         ✶ ⟦⟦ treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ⟧⟧)
        ✶ ⟦⟦ treeseq_pred
               (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
                  dstname dummy9) dummy3 ⟧⟧)
   ⋁ crash_xform
       (exists
          (t : treeseq_one) (ts'' : nelist treeseq_one) (dfile : dirfile) dummy4',
          ((⟦⟦ dummy3 = pushd t ts'' ⟧⟧
            ✶ ⟦⟦ treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ⟧⟧)
           ✶ ⟦⟦ tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
                  dstname dfile t ⟧⟧)
          ✶ ⟦⟦ treeseq_pred
                 (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4' dstbase
                    dstname dummy9) ts'' ⟧⟧).
Proof.
(* original proof tokens: 122 *)

(* No more tactics to try *)
Admitted.

Lemma proto_bytefile_nonnil: forall f pfy ufy fy block_off byte_off data F,
	      proto_bytefile_valid f pfy ->
	      unified_bytefile_valid pfy ufy ->
	      rep f fy ->
	      (F * arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off) data)%pred
       (list2nmem (ByFData fy)) -> 
       length data > 0 ->
       byte_off < valubytes ->
	      selN (PByFData pfy) block_off nil <> [].
(* hint proof tokens: 234 *)
Proof.
	    intros.
	    erewrite proto_bytefile_unified_bytefile_selN; eauto.
	    unfold get_sublist, not; intros.
	    pose proof valubytes_ge_O as Hx.
	    eapply firstn_nonnil in Hx.
	    split_hypothesis.
	    rewrite H6 in H5.
	    inversion H5.
	    
	    unfold not; intros Hy.
	    assert (A: (block_off * valubytes) < length (UByFData ufy)).
	    erewrite unified_byte_protobyte_len with (k:= valubytes); eauto.
	    apply mult_lt_compat_r; auto.
	    erewrite bfile_protobyte_len_eq; eauto.
	    eapply inlen_bfile with (j:= byte_off); eauto.
	    
	    eapply skipn_nonnil in A.
	    split_hypothesis.
	    rewrite H6 in Hy.
	    inversion Hy.

	  erewrite bfile_protobyte_len_eq; eauto.
	  eapply inlen_bfile with (j:= byte_off); eauto.
  Qed.
Lemma length_le_middle: forall a b c,
  a = b * valubytes ->
  c < b ->
  valubytes <= a - c * valubytes.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma map_app_firstn_skipn: forall {A B} (data: list (A * B)) m,
  (map fst (firstn (m * valubytes) data) ++
   map fst (firstn valubytes (skipn (m * valubytes) data)))%list =
   map fst (firstn (valubytes + m * valubytes) data).
Proof.
(* original proof tokens: 102 *)

(* No more tactics to try *)
Admitted.

Lemma bound_le_exfalso: forall F f fy off data,
        rep f fy ->
        (off < # (INODE.ABytes (DFAttr f)) -> False) ->
        (F * arrayN (ptsto (V:=byteset)) off data)%pred
       (list2nmem (ByFData fy)) -> 
       0 < length data ->
       False.
(* hint proof tokens: 68 *)
Proof.
      intros; unfold rep in *; split_hypothesis.
      apply list2nmem_arrayN_bound in H1.
      destruct H1.
      apply length_zero_iff_nil in H1; lia.
      rewrite H5 in H6; rewrite H6 in H0; lia.
  Qed.
Lemma arrayN_app_merge: forall Fd a head_data old_data tail_data,
(((Fd ✶ arrayN (ptsto (V:=byteset)) (a) head_data)
      ✶ arrayN (ptsto (V:=byteset)) (a + length head_data) old_data)
      ✶ arrayN (ptsto (V:=byteset)) (a + length head_data + length old_data) tail_data) 
      =p=> Fd ✶ arrayN (ptsto (V:=byteset)) (a) (head_data ++ old_data ++ tail_data).
(* hint proof tokens: 36 *)
Proof.
  intros.
  rewrite sep_star_assoc.
  rewrite <- arrayN_app.
  rewrite sep_star_assoc.
  rewrite <- arrayN_app; auto.
Qed.
Lemma list2nmem_arrayN_bound_app_middle: forall Fd a head_data old_data tail_data l,
  length old_data > 0 ->
  (Fd ✶ arrayN (ptsto (V:=byteset)) a 
    (head_data ++ old_data ++ tail_data))%pred (list2nmem l) ->
  a + (length head_data + (length old_data + length tail_data)) <= length l.
(* hint proof tokens: 60 *)
Proof.
  intros.
  apply list2nmem_arrayN_bound in H0 as Hx; destruct Hx.
  apply length_zero_iff_nil in H1; repeat rewrite app_length in H1; lia.
  repeat rewrite app_length in H1; auto.
Qed.
Lemma rep_modified_exists: forall f f' pfy ufy fy block_off head_data data old_data tail_data Fd,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  ByFAttr fy = DFAttr f ->
  # (INODE.ABytes (ByFAttr fy)) = length (ByFData fy) ->
  roundup (length (ByFData fy)) valubytes =
      length (DFData f) * valubytes ->
  length old_data = length data ->
  length data > 0 ->
  length head_data + length data <= valubytes ->
  DFAttr f' = DFAttr f ->
      (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
✶ arrayN (ptsto (V:=byteset))
    (block_off * valubytes + length head_data) old_data)
✶ arrayN (ptsto (V:=byteset))
   (block_off * valubytes + length head_data +
    length old_data) tail_data)%pred (list2nmem (ByFData fy)) ->
  (diskIs (mem_except (list2nmem (DFData f)) block_off)
✶ block_off
 |-> (list2valu
        (firstn (length head_data)
           (valu2list (fst (selN (DFData f) block_off valuset0))) ++
         data ++
         skipn (length head_data + length data)
           (valu2list (fst (selN (DFData f) block_off valuset0)))),
     vsmerge (selN (DFData f) block_off valuset0)))%pred (list2nmem (DFData f')) ->
 rep f' {| ByFData:= firstn (length (ByFData fy)) (concat (updN (PByFData pfy) block_off 
                                  (valuset2bytesets ((list2valu
                                    (firstn (length head_data) 
                                    (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                                    data ++
                                     skipn (length head_data + length data)
                                       (valu2list (fst (selN (DFData f) block_off valuset0)))%list),
                                 vsmerge (selN (DFData f) block_off valuset0))))));
                     ByFAttr:= ByFAttr fy |}.
(* hint proof tokens: 755 *)
Proof.
  intros.
  exists({| PByFData:= (updN (PByFData pfy) block_off 
                            (valuset2bytesets ((list2valu
                              (firstn (length head_data) 
                              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                              data ++
                               skipn (length head_data + length data)
                                 (valu2list (fst (selN (DFData f) block_off valuset0)))%list),
                           vsmerge (selN (DFData f) block_off valuset0))))) |}).
                           
  exists ({| UByFData:= concat (updN (PByFData pfy) block_off 
                                    (valuset2bytesets ((list2valu
                                      (firstn (length head_data) 
                                      (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                                      data ++
                                       skipn (length head_data + length data)
                                         (valu2list (fst (selN (DFData f) block_off valuset0)))%list),
                                   vsmerge (selN (DFData f) block_off valuset0))))) |}).

  match goal with | [H: (((_ ✶ _) ✶ _) ✶ _)%pred _ |- _] => apply arrayN_app_merge in H end.
  match goal with | [H: (_ * arrayN _ _ (_++_++_))%pred _ |- _] => 
  apply list2nmem_arrayN_bound_app_middle in H as Hx end.
  intuition.
  unfold proto_bytefile_valid; simpl.
  rewrite_proto.
  rewrite <- map_updN.
  match goal with | [H: (diskIs _ * _)%pred _ |- _] => apply diskIs_ptsto_updN in H end.
  match goal with | [H: DFData ?f = _ |- context[DFData ?f] ] => rewrite H end; auto.
  eapply inlen_bfile with (j:= length head_data); eauto.
  solve_rep.
  lia.
  instantiate (1:= old_data).
  lia.
  pred_apply; repeat rewrite arrayN_app; cancel.

  unfold unified_bytefile_valid; simpl.
  reflexivity.

  unfold bytefile_valid; simpl.
  length_rewrite_l; auto.
  erewrite <- unified_byte_protobyte_len; eauto.
  eapply bytefile_unified_byte_len; eauto.

  simpl; match goal with | [H: ByFAttr _ = _ |- _] => rewrite H end; auto.
  simpl; length_rewrite_l; auto.
  erewrite <- unified_byte_protobyte_len; eauto.
  eapply bytefile_unified_byte_len; eauto.

  simpl; match goal with | [H: (diskIs _ * _)%pred _ |- _] => apply diskIs_ptsto_updN in H end.
          match goal with | [H: DFData ?f = _ |- context[DFData ?f] ] => rewrite H end; auto.
  length_rewrite_l; auto.
  erewrite <- unified_byte_protobyte_len; eauto.
  eapply bytefile_unified_byte_len; eauto.
  eapply inlen_bfile with (j:= length head_data); eauto.
  solve_rep.
  lia.
  instantiate (1:= old_data).
  lia.
  pred_apply; repeat rewrite arrayN_app; cancel.
  lia.
Qed.
Lemma dsupd_dsupd_iter_dwrite_middle: forall inum Ftree ts pathname fy ds bnl data f bn f' block_off Fd tail_data old_data,
  rep f fy ->
  length data > 0 ->
  length old_data = length data ->
  ((Fd
   ✶ (arrayN (ptsto (V:=byteset)) (block_off * valubytes)
        (firstn (length data / valubytes * valubytes) old_data)
      ✶ arrayN (ptsto (V:=byteset))
          ((block_off + length data / valubytes) * valubytes)
          (skipn (length data / valubytes * valubytes) old_data)))
  ✶ arrayN (ptsto (V:=byteset))
      (block_off * valubytes + length old_data) tail_data)%pred
   (list2nmem (ByFData fy)) ->
  0 < length (skipn (length data / valubytes * valubytes) data) ->
  length bnl = length data / valubytes ->
  (Ftree ✶ pathname |-> File inum f')%pred
    (dir2flatmem2
       (TStree
          (tsupd_iter ts pathname block_off
             (combine
                (map list2valu
                   (list_split_chunk (length data / valubytes)
                      valubytes
                      (firstn
                         (length data / valubytes * valubytes)
                         data)))
                (map vsmerge
                   (get_sublist (DFData f) block_off
                      (length data / valubytes))))) !!)) ->
  (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
  tree_names_distinct (TStree ts !!) ->
  0 < length data / valubytes ->
  dsupd
    (dsupd_iter ds bnl
       (combine
          (map list2valu
             (list_split_chunk (length data / valubytes) valubytes
                (firstn (length data / valubytes * valubytes) data)))
          (map vsmerge
             (get_sublist (DFData f) block_off
                (length data / valubytes))))) bn
    (list2valu
       (skipn (length data / valubytes * valubytes) data ++
        skipn
          (length
             (skipn (length data / valubytes * valubytes) data))
          (valu2list
             (fst (selN (DFData f') (block_off + length data / valubytes) valuset0)))),
    vsmerge (selN (DFData f') (block_off + length data / valubytes) valuset0)) =
  dsupd_iter ds (bnl ++ [bn])
    (combine
       (map list2valu
          (list_split_chunk
             (roundup (length data) valubytes / valubytes) valubytes
             (data ++
              skipn (length data mod valubytes)
                (valu2list
                   (fst
                      (selN (DFData f) (block_off + length data / valubytes) valuset0))))))
       (map vsmerge
          (firstn (roundup (length data) valubytes / valubytes)
             (skipn block_off (DFData f))))).
(* hint proof tokens: 372 *)
Proof.
      intros.
     assert (A: block_off + length data / valubytes <= length (DFData f)).
      apply Nat.lt_le_incl; eapply inlen_bfile with (j:= 0); eauto.
     apply valubytes_ge_O.
     2: rewrite <- plus_n_O; pred_apply; cancel.
     length_rewrite_l.
     match goal with | [H: 0 < length (skipn _ _) |- _] => 
        rewrite skipn_length in H end; lia.
   

     erewrite dsupd_iter_dsupd_tail; [ | solve_eq_dwrite_middle ]. 
      rewrite <- combine_app_tail; [ | solve_eq_dwrite_middle ].
      simpl.
    
    length_rewrite_l.
    repeat rewrite map_app_tail.
    rewrite <- list_split_chunk_app_1; solve_eq_dwrite_middle.
    rewrite mod_eq'; eauto.
    simpl_skipn_lt.
    erewrite <- bfile_selN_tsupd_iter_eq with (f:= f)(f':= f'); eauto; [ |
   unfold datatype; solve_eq_dwrite_middle]. 
    rewrite <- get_sublist_app_tail.
    rewrite roundup_div_S_eq; unfold get_sublist; eauto.
    rewrite app_assoc; rewrite firstn_skipn.
    rewrite Nat.add_1_r; eauto.
    
   eapply inlen_bfile_S; eauto.
   pred_apply; cancel.
   rewrite skipn_length; 
   repeat match goal with | [H: ?a = _ |- context[?a] ] => rewrite H; auto end.
   rewrite mod_eq'; auto.
   rewrite <-  le_plus_minus; auto.
   rewrite mod_eq'; auto.
   apply mod_upper_bound_le'; auto.
 Qed.
Lemma dsupd_dsupd_iter_dwrite_middle2: forall x inum Ftree ts pathname fy ds bnl data f f' block_off Fd tail_data old_data,
  rep f fy ->
  length data > 0 ->
  length old_data = length data ->
  ((Fd
   ✶ (arrayN (ptsto (V:=byteset)) (block_off * valubytes)
        (firstn (length data / valubytes * valubytes) old_data)
      ✶ arrayN (ptsto (V:=byteset))
          ((block_off + length data / valubytes) * valubytes)
          (skipn (length data / valubytes * valubytes) old_data)))
  ✶ arrayN (ptsto (V:=byteset))
      (block_off * valubytes + length old_data) tail_data)%pred
   (list2nmem (ByFData fy)) ->
  0 < length (skipn (length data / valubytes * valubytes) data) ->
  length bnl = length data / valubytes ->
  (Ftree ✶ pathname |-> File inum f')%pred
    (dir2flatmem2
       (TStree
          (tsupd_iter ts pathname block_off
             (combine
                (map list2valu
                   (list_split_chunk (length data / valubytes)
                      valubytes
                      (firstn
                         (length data / valubytes * valubytes)
                         data)))
                (map vsmerge
                   (get_sublist (DFData f) block_off
                      (length data / valubytes))))) !!)) ->
  (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
  tree_names_distinct (TStree ts !!) ->
  0 < length data / valubytes ->
  dsupd
  (dsupd_iter ds bnl
     (combine
        (map list2valu
           (list_split_chunk (length data / valubytes) valubytes
              (firstn (length data / valubytes * valubytes) data)))
        (map vsmerge
           (get_sublist (DFData f) block_off
              (length data / valubytes))))) x
  (list2valu
     (skipn (length data / valubytes * valubytes) data ++
      skipn
        (length
           (skipn (length data / valubytes * valubytes) data))
        (valu2list
           (fst (selN (DFData f') (block_off + length data / valubytes) valuset0)))),
  vsmerge (selN (DFData f') (block_off + length data / valubytes) valuset0)) =
dsupd_iter ds (bnl ++ [x])%list
  (combine
     (map list2valu
        (list_split_chunk  (S (length data / valubytes)) valubytes
           (firstn ( (S (length data / valubytes)) * valubytes)
              (data ++
               skipn (length data mod valubytes)
                 (valu2list
                    (fst
                       (selN (DFData f) (block_off + length data / valubytes) valuset0)))))))
     (map vsmerge (get_sublist (DFData f) block_off  (S (length data / valubytes))))).
Proof.
(* original proof tokens: 440 *)

(* No more tactics to try *)
Admitted.

Lemma tsupd_tsupd_iter_dwrite_middle2: forall Ftree inum Fd old_data tail_data ts pathname block_off data f fy f' fy',
   rep f fy ->
   rep f' fy' ->
   0 < length (skipn (length data / valubytes * valubytes) data) ->
   length old_data = length data ->
   tree_names_distinct (TStree ts !!) ->
   length data > 0 ->
   0 < length data / valubytes ->
   ((Fd
       ✶ (arrayN (ptsto (V:=byteset)) (block_off * valubytes)
            (firstn (length data / valubytes * valubytes) old_data)
          ✶ arrayN (ptsto (V:=byteset))
              ((block_off + length data / valubytes) * valubytes)
              (skipn (length data / valubytes * valubytes) old_data)))
      ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length old_data) tail_data)%pred
       (list2nmem (ByFData fy)) ->
   min (length (ByFData fy) - (block_off * valubytes + length data))
       (hpad_length (length data)) = length tail_data ->
    (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
    (Ftree ✶ pathname |-> File inum f')%pred
        (dir2flatmem2
           (TStree
              (tsupd_iter ts pathname block_off
                 (combine
                    (map list2valu
                       (list_split_chunk (length data / valubytes)
                          valubytes
                          (firstn
                             (length data / valubytes * valubytes)
                             data)))
                    (map vsmerge
                       (get_sublist (DFData f) block_off
                          (length data / valubytes))))) !!)) ->
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
        (length
           (skipn (length data / valubytes * valubytes) data))
        (valu2list
           (fst (selN (DFData f') (block_off + length data / valubytes ) valuset0))))%list,
  vsmerge (selN (DFData f') (block_off + length data / valubytes ) valuset0)) =
tsupd_iter ts pathname block_off
  (combine
     (map list2valu
        (list_split_chunk (S (length data / valubytes)) valubytes
           (firstn (S (length data / valubytes) * valubytes)
              (data ++
               skipn (length data mod valubytes)
                 (valu2list
                    (fst (selN (DFData f) (block_off + length data / valubytes ) valuset0)))))))
     (map vsmerge
        (get_sublist (DFData f) block_off
           (S (length data / valubytes))))).
(* hint proof tokens: 356 *)
Proof.
   intros.
   erewrite <- bfile_selN_tsupd_iter_eq; eauto.
   rewrite firstn_app_le.
   rewrite firstn_oob with (n:= (S (length data / valubytes) * valubytes - length data)).
   repeat rewrite <- roundup_div_S_eq; auto.
   unfold get_sublist.
   eapply tsupd_tsupd_iter_merge'; eauto.
   simpl_skipn_lt.

   length_rewrite_l.
   apply Nat.le_add_le_sub_l.
  rewrite Nat.add_sub_assoc.
  rewrite Nat.add_sub_swap.
  rewrite  sub_mod_eq_round; auto.
  lia.
  apply Nat.mod_le; auto.
  apply mod_upper_bound_le'; auto.
  rewrite <- roundup_div_S_eq; auto.
  rewrite mul_div; auto.
  apply roundup_ge; auto.
   apply roundup_mod_0; auto.
   simpl_skipn_lt.
 
   unfold datatype; length_rewrite_l.
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   
   apply Nat.lt_le_incl.
   eapply inlen_bfile with (j:= 0); eauto.
   apply valubytes_ge_O.
   2: rewrite <- plus_n_O; pred_apply; cancel.
   
   length_rewrite_l.
   rewrite H2.
   rewrite skipn_length in H1; auto.
   
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
Qed.
Ltac simpl_skipn_zero:=
match goal with
  | [H: 0 < length (skipn _ _) -> False |- _] =>
  apply Nat.nlt_ge in H;
  rewrite skipn_length in H; rewrite Nat.mul_comm in H;
  rewrite <- Nat.mod_eq in H; auto; inversion H
end.
Ltac simpl_min_zero:=
match goal with
  | [H: min _ _ = _,
      H0 : _ = 0 |- _] =>
  unfold hpad_length in H;
  rewrite H0 in H; simpl in H;
  rewrite Nat.min_0_r in H; symmetry in H;
  apply length_zero_iff_nil in H
end.
Lemma dsupd_eq_dwrite_middle:  forall ts Fd pathname inum Ftree old_data tail_data ds bn data f fy block_off,
        rep f fy ->
         length old_data = length data ->
         length data > 0 ->
         length data / valubytes = 0 ->
        ((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)
      ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length old_data) tail_data)%pred
       (list2nmem (ByFData fy)) ->
         min (length (ByFData fy) - (block_off * valubytes + length data))
             (hpad_length (length data)) = length tail_data ->
          (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->

              dsupd ds bn
                  (list2valu
                     (data ++
                      skipn (length data)
                        (valu2list (fst (selN (DFData f) block_off valuset0)))),
                  vsmerge (selN (DFData f) block_off valuset0)) =
                match
                  combine
                    (map list2valu
                       (list_split_chunk
                          (roundup (length data) valubytes / valubytes) valubytes
                          (data ++
                           skipn (length data mod valubytes)
                             (valu2list (fst (selN (DFData f) block_off valuset0))))))
                    (map vsmerge
                       (firstn (roundup (length data) valubytes / valubytes)
                          (skipn block_off (DFData f))))
                with
                | [] => ds
                | [h] => dsupd ds bn h
                | h :: _ :: _ => dsupd ds bn h
                end.
Proof.
(* original proof tokens: 244 *)

(* No more tactics to try *)
Admitted.

Lemma tsupd_eq_dwrite_middle:  forall ts Fd pathname inum Ftree old_data tail_data data f fy block_off,
        rep f fy ->
         length old_data = length data ->
         length data > 0 ->
         length data / valubytes = 0 ->
        ((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)
      ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length old_data) tail_data)%pred
       (list2nmem (ByFData fy)) ->
         min (length (ByFData fy) - (block_off * valubytes + length data))
             (hpad_length (length data)) = length tail_data ->
          (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->

            tsupd ts pathname block_off
  (list2valu
     (data ++
      skipn (length data)
        (valu2list (fst (selN (DFData f)  block_off  valuset0)))),
  vsmerge (selN (DFData f)  block_off  valuset0)) =
tsupd_iter ts pathname block_off
  (combine
     (map list2valu
        (list_split_chunk
           (roundup (length data) valubytes / valubytes) valubytes
           (data ++
            skipn (length data mod valubytes)
              (valu2list
                 (fst
                    (selN (DFData f)
                    ( block_off + length data / valubytes ) valuset0))))))
     (map vsmerge
        (firstn (roundup (length data) valubytes / valubytes)
           (skipn block_off (DFData f))))).
Proof.
(* original proof tokens: 251 *)
unfold tsupd, tsupd_iter; simpl; intros.
(* No more tactics to try *)
Admitted.

Lemma skipn_not_nil': forall Fd f fy (data: list byte) 
               head_data old_data tail_data block_off,
    length head_data < valubytes
    -> length old_data = length data
    -> length data > 0
    -> rep f fy
    -> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
        ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length head_data) old_data)
        ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length head_data + length data) 
          tail_data)%pred (list2nmem (ByFData fy))
    -> skipn block_off (DFData f) <> [].
(* hint proof tokens: 90 *)
Proof.
  intros.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); [eauto|eauto| |pred_apply; cancel].
  lia.
  unfold not; intros D.
  apply skipn_eq_nil in D.
  destruct D; try lia.
  apply length_zero_iff_nil in H4.
  lia.
Qed.
Lemma dsupd_dsupd_iter_eq_dwrite_first: forall Fd 
            (old_data tail_data head_data: list byteset) (data: list byte)
                   ds bn block_off f fy,
  length head_data < valubytes
  -> length old_data = length data
  -> length data > 0
  -> rep f fy
  -> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data) old_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data + length data) 
        tail_data)%pred (list2nmem (ByFData fy))
  -> length data <= valubytes - length head_data
  -> dsupd ds bn (list2valu
           (firstn (length head_data) (valu2list 
              (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn (length head_data + length data)
              (valu2list (fst (selN (DFData f) block_off valuset0)))),
        vsmerge (selN (DFData f) block_off valuset0)) =
      dsupd_iter ds [bn]
        (combine (map list2valu (list_split_chunk 
          (roundup (length (firstn (length head_data)
                (valu2list (fst (selN (DFData f) block_off valuset0)))) +
                 length data) valubytes / valubytes) valubytes
           (firstn (length head_data)
              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn (tpad_length (length head_data + length data))
              (valu2list (fst (selN (DFData f)
                    (block_off + (length head_data + length data) / valubytes)
                    valuset0))))))
     (map vsmerge (firstn (roundup (length (firstn (length head_data)
                (valu2list (fst (selN (DFData f) block_off valuset0)))) +
                 length data) valubytes / valubytes) (skipn block_off (DFData f))))).
Proof.
(* original proof tokens: 438 *)
unfold dsupd_iter, dsupd; simpl.
(* No more tactics to try *)
Admitted.

Lemma tsupd_tsupd_iter_eq_dwrite_first: forall ts Fd pathname
            (old_data tail_data head_data: list byteset) (data: list byte)
                   block_off f fy,
  length head_data < valubytes
  -> length old_data = length data
  -> length data > 0
  -> rep f fy
  -> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data) old_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data + length data) 
        tail_data)%pred (list2nmem (ByFData fy))
  -> length data <= valubytes - length head_data
  -> tsupd ts pathname block_off (list2valu
           (firstn (length head_data) (valu2list 
              (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn (length head_data + length data)
              (valu2list (fst (selN (DFData f) block_off valuset0)))),
        vsmerge (selN (DFData f) block_off valuset0)) =
      tsupd_iter ts pathname block_off
        (combine (map list2valu (list_split_chunk 
          (roundup (length (firstn (length head_data)
                (valu2list (fst (selN (DFData f) block_off valuset0)))) +
                 length data) valubytes / valubytes) valubytes
           (firstn (length head_data)
              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn (tpad_length (length head_data + length data))
              (valu2list (fst (selN (DFData f)
                    (block_off + (length head_data + length data) / valubytes)
                    valuset0))))))
     (map vsmerge (firstn (roundup (length (firstn (length head_data)
                (valu2list (fst (selN (DFData f) block_off valuset0)))) +
                 length data) valubytes / valubytes) (skipn block_off (DFData f))))).
Proof.
(* original proof tokens: 438 *)
unfold tsupd, tsupd_iter; simpl; intros.
(* No more tactics to try *)
Admitted.

Lemma crash_dwrite_first1: forall Fd Fm Ftop fsxp 
                ds ts sm realcrash F_ hm' crash pathname mscs hm0 l
                (old_data tail_data head_data: list byteset) (data: list byte)
                 block_off f fy,
length head_data < valubytes
-> length old_data = length data
-> length data > 0
-> rep f fy
-> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
    ✶ arrayN (ptsto (V:=byteset))
      (block_off * valubytes + length head_data) old_data)
    ✶ arrayN (ptsto (V:=byteset))
      (block_off * valubytes + length head_data + length data) 
      tail_data)%pred (list2nmem (ByFData fy))
-> length data <= valubytes - length head_data
-> treeseq_in_ds Fm Ftop fsxp sm mscs ts ds
-> hashmap_subset l hm0 hm'
-> (forall (realcrash : rawpred) (hm' : hashmap),
   crash_xform realcrash
   =p=> crash_xform
        (exists (i : addr) (ds' : diskset) 
              (ts' : treeseq) (mscs' : BFile.BFILE.memstate) sm' (bnl : list addr),
           (((((LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm'
    ✶ ⟦⟦ i <= roundup (length (firstn (length head_data)
                 (valu2list (fst (selN (DFData f) block_off valuset0)))) + 
                 length data) valubytes / valubytes ⟧⟧)
   ✶ ⟦⟦ ds' = dsupd_iter ds bnl
          (combine (map list2valu (list_split_chunk i valubytes
                   (firstn (i * valubytes) (firstn (length head_data)
                         (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                       data ++
                       skipn (tpad_length
                            (length head_data + length data))
                         (valu2list (fst (selN (DFData f)
                                (block_off + (length head_data +
                                  length data) / valubytes) valuset0)))))))
             (map vsmerge (get_sublist (DFData f) block_off i))) ⟧⟧)
  ✶ ⟦⟦ ts' = tsupd_iter ts pathname block_off
         (combine (map list2valu (list_split_chunk i valubytes
                  (firstn (i * valubytes) (firstn (length head_data)
                        (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                      data ++
                      skipn (tpad_length
                           (length head_data + length data))
                        (valu2list (fst (selN (DFData f)
                                (block_off + (length head_data +
                                  length data) / valubytes) valuset0)))))))
            (map vsmerge (get_sublist (DFData f) block_off i)))⟧⟧) 
  ✶ ⟦⟦ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ⟧⟧)
  ✶ ⟦⟦ length bnl = i ⟧⟧)
  ✶ ⟦⟦ MSAlloc mscs' = MSAlloc mscs ⟧⟧) ->
     (F_ ✶ realcrash) * ⟦⟦ exists l : list (word hashlen * {sz : addr & word sz}),
      hashmap_subset l hm0 hm' ⟧⟧  =p=> crash hm')
-> crash_xform realcrash
    =p=> crash_xform
       (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
        ⋁ (exists (bn : addr) (ds' : diskset) (ts' : treeseq) (mscs' : BFile.BFILE.memstate) sm',
     (((LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm'
        ✶ ⟦⟦ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ⟧⟧)
       ✶ ⟦⟦ ds' = dsupd ds bn (list2valu
                 (firstn (length head_data) 
                    (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                  data ++
                  skipn
                    (length head_data + length data)
                    (valu2list (fst (selN (DFData f) block_off valuset0)))),
              vsmerge (selN (DFData f) block_off valuset0)) ⟧⟧)
      ✶ ⟦⟦ ts' = tsupd ts pathname block_off (list2valu
                (firstn (length head_data)
                   (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                 data ++
                 skipn (length head_data + length data)
                   (valu2list (fst (selN (DFData f) block_off valuset0)))),
             vsmerge (selN (DFData f) block_off valuset0)) ⟧⟧)
     ✶ ⟦⟦ MSAlloc mscs' = MSAlloc mscs ⟧⟧))
-> realcrash ✶ F_ ⇨⇨ crash hm'.
(* hint proof tokens: 2178 *)
Proof.
  intros.
  repeat xcrash_rewrite.
  xform_norm; xform_normr; cancel.
- repeat (rewrite crash_xform_exists_comm; cancel).
  repeat (rewrite crash_xform_sep_star_dist;
  rewrite crash_xform_lift_empty).
  safecancel.
  instantiate (1:= 0).
  lia.
  simpl.
  instantiate(1:= nil); eauto.
  all: simpl; eauto.

- repeat (rewrite crash_xform_exists_comm; cancel).
  repeat (rewrite crash_xform_sep_star_dist;
  rewrite crash_xform_lift_empty).
  safecancel.
  instantiate (1:= length [x]).
  match goal with |[H: _ <= _ - _ |- _] => apply le_sub_le_add_l' in H end.
  rewrite roundup_lt_one; auto.
  rewrite Nat.div_same; auto.
  lia.
  length_rewrite_l.
  lia.
  
  match goal with |[H: _ <= _ - _ |- _] => apply le_sub_le_add_l' in H end.
    unfold tpad_length.
    inversion H4.
    rewrite H10 in *.
    rewrite Nat.mod_same; simpl; auto.
    rewrite skipn_oob.
    rewrite skipn_oob.
    rewrite app_nil_r.
    rewrite <- plus_n_O.
    rewrite firstn_oob with (n:= valubytes); eauto.
    rewrite firstn_oob with (n:= valubytes); eauto.
    simpl.
    destruct (map vsmerge (get_sublist (DFData f) block_off 1)) eqn:D.
    apply map_eq_nil in D; unfold get_sublist in D; 
    apply firstn_eq_nil in D.
    destruct D; [lia | ].
     apply skipn_eq_nil in H9.
     destruct H9.
     assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    lia.
    exfalso; eapply le_lt_false.
    apply H9. apply A.
    
    apply length_zero_iff_nil in H9.
       assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    lia.
    unfold datatype in A; rewrite H9 in A; inversion A.
    simpl in D.
    unfold get_sublist in D; erewrite firstn_1_selN in D.
    simpl in D.
    rewrite skipn_selN in D; rewrite <- plus_n_O in D.
    inversion D.
    instantiate(2:= [x]); simpl; eauto.
    
    eapply skipn_not_nil'; eauto.
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.
    
    length_rewrite_l.
      unfold tpad_length.
    rewrite H9 in *.
    rewrite Nat.mod_small; auto; try lia.
    destruct (length head_data + length data) eqn:D; try lia.
    simpl; unfold get_sublist.
    erewrite firstn_1_selN.
    rewrite skipn_selN; rewrite <- plus_n_O.
    replace (S n / valubytes) with 0. repeat rewrite <- plus_n_O.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    length_rewrite_l.
    destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
    simpl; lia.
    rewrite Nat.add_assoc.
    rewrite D.
    length_rewrite_l.
    assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
    rewrite D0; auto.
    rewrite valu2list_len in A.
    simpl in A.
    rewrite <- le_plus_minus; lia.
    length_rewrite_l.
    destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
    apply length_zero_iff_nil in D0; rewrite valu2list_len in D0; rewrite valubytes_is in D0.
    simpl in *; lia.
    rewrite Nat.add_assoc.
    rewrite D.
    length_rewrite_l.
    assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
    rewrite D0; auto.
    rewrite valu2list_len in A.
    simpl in A.
    rewrite <- le_plus_minus; lia.
    symmetry; apply Nat.div_small_iff; auto; lia.
    unfold not; intros D1.
    apply skipn_eq_nil in D1.
    destruct D1.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    lia.
    lia.
    apply length_zero_iff_nil in H12.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    lia.
    lia.
    auto.
    length_rewrite_l.
    length_rewrite_l.
    2: eauto.

    match goal with |[H: _ <= _ - _ |- _] => apply le_sub_le_add_l' in H end.
    unfold tpad_length.
    inversion H4.
    rewrite H10 in *.
    rewrite Nat.mod_same; simpl; auto.
    rewrite skipn_oob.
    rewrite skipn_oob.
    rewrite app_nil_r.
    rewrite <- plus_n_O.
    rewrite firstn_oob with (n:= valubytes); eauto.
    rewrite firstn_oob with (n:= valubytes); eauto.
    simpl.
    destruct (map vsmerge (get_sublist (DFData f) block_off 1)) eqn:D.
    apply map_eq_nil in D; unfold get_sublist in D; 
    apply firstn_eq_nil in D.
    destruct D; [lia | ].
    apply skipn_eq_nil in H9.
    destruct H9.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    lia.
    exfalso; eapply le_lt_false.
    apply H9. apply A.
    
    apply length_zero_iff_nil in H9.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    lia.
    unfold datatype in A; rewrite H9 in A; inversion A.
    simpl in D.
    unfold get_sublist in D; erewrite firstn_1_selN in D.
    simpl in D.
    rewrite skipn_selN in D; rewrite <- plus_n_O in D.
    inversion D.
    simpl; eauto.
    
    eapply skipn_not_nil'; eauto.
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.

    length_rewrite_l.
    unfold tpad_length.
    rewrite H9 in *.
    rewrite Nat.mod_small; auto; try lia.
    destruct (length head_data + length data) eqn:D; try lia.
    simpl; unfold get_sublist.
    erewrite firstn_1_selN.
    rewrite skipn_selN; rewrite <- plus_n_O.
    replace (S n / valubytes) with 0. repeat rewrite <- plus_n_O.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    length_rewrite_l.
    destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
    simpl; lia.
    rewrite Nat.add_assoc.
    rewrite D.
    length_rewrite_l.
    assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
    rewrite D0; auto.
    rewrite valu2list_len in A.
    simpl in A.
    rewrite <- le_plus_minus; lia.
    length_rewrite_l.
    destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
    apply length_zero_iff_nil in D0; rewrite valu2list_len in D0; rewrite valubytes_is in D0.
    simpl in *; lia.
    rewrite Nat.add_assoc.
    rewrite D.
    length_rewrite_l.
    assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
    rewrite D0; auto.
    rewrite valu2list_len in A.
    simpl in A.
    rewrite <- le_plus_minus; lia.
    symmetry; apply Nat.div_small_iff; auto; lia.
    unfold not; intros D1.
    apply skipn_eq_nil in D1.
    destruct D1.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    lia.
    lia.
    apply length_zero_iff_nil in H12.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    lia.
    lia.
    auto.
    length_rewrite_l.
    length_rewrite_l.
    auto.
Qed.
Lemma dsupd_iter_dsupd_dwrite_first: forall Ftree Fd (old_data tail_data head_data: list byteset) (data: list byte) ds bn bnl block_off f f' fy pathname inum ts,
    length head_data < valubytes
  -> length old_data = length data
  -> length data > 0
  -> (length data <= valubytes - length head_data -> False)
  -> rep f fy
  -> tree_names_distinct (TStree ts !!)
  -> (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!))
  -> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data) old_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data + length data) 
        tail_data)%pred (list2nmem (ByFData fy))
  -> (Ftree ✶ pathname |-> File inum f')%pred
        (dir2flatmem2
           (TStree
              (tsupd ts pathname block_off
                 (list2valu
                    (firstn (length head_data)
                       (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                     firstn (valubytes - length head_data) data ++
                     skipn
                       (length head_data +
                        length
                          (firstn (valubytes - length head_data)
                             data))
                       (valu2list (fst (selN (DFData f) block_off valuset0)))),
                 vsmerge (selN (DFData f) block_off valuset0))) !!))
  -> dsupd_iter
  (dsupd ds bn
     (list2valu
        (firstn (length head_data)
           (valu2list (fst (selN (DFData f) block_off valuset0))) ++
         firstn (valubytes - length head_data) data ++
         skipn
           (length head_data +
            (valubytes - length head_data))
           (valu2list (fst (selN (DFData f) block_off valuset0)))),
     vsmerge (selN (DFData f) block_off valuset0))) bnl
  (combine
     (map list2valu
        (list_split_chunk
           (roundup
              (length data -
               (valubytes - length head_data)) valubytes /
            valubytes) valubytes
           (skipn (valubytes - length head_data) data ++
            skipn
              ((length data -
                (valubytes - length head_data)) mod valubytes)
              (valu2list
                 (fst
                    (selN (DFData f') (block_off + 1 +
                      (length data -
                       (valubytes - length head_data)) / valubytes)
                    valuset0))))))
     (map vsmerge
        (firstn
           (roundup
              (length data -
               (valubytes - length head_data)) valubytes /
            valubytes) (skipn (block_off + 1) (DFData f'))))) =
dsupd_iter ds (bn :: bnl)
  (combine
     (map list2valu
        (list_split_chunk
           (roundup
              (length
                 (firstn (length head_data)
                    (valu2list (fst (selN (DFData f) block_off valuset0)))) +
               length data) valubytes / valubytes) valubytes
           (firstn (length head_data)
              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn
              (tpad_length
                 (length head_data + length data))
              (valu2list
                 (fst
                    (selN (DFData f)(block_off +
                      (length head_data + length data) /
                      valubytes) valuset0))))))
     (map vsmerge
        (firstn
           (roundup
              (length
                 (firstn (length head_data)
                    (valu2list (fst (selN (DFData f) block_off valuset0)))) +
               length data) valubytes / valubytes)
           (skipn block_off (DFData f))))).
Proof.
(* original proof tokens: 866 *)

(* No more tactics to try *)
Admitted.

Lemma tsupd_iter_tsupd_dwrite_first: forall Ftree Fd (old_data tail_data head_data: list byteset) (data: list byte) block_off f f' fy pathname inum ts,
    length head_data < valubytes
  -> length old_data = length data
  -> length data > 0
  -> (length data <= valubytes - length head_data -> False)
  -> rep f fy
  -> tree_names_distinct (TStree ts !!)
  -> (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!))
  -> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data) old_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data + length data) 
        tail_data)%pred (list2nmem (ByFData fy))
  -> (Ftree ✶ pathname |-> File inum f')%pred
        (dir2flatmem2
           (TStree
              (tsupd ts pathname block_off
                 (list2valu
                    (firstn (length head_data)
                       (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                     firstn (valubytes - length head_data) data ++
                     skipn
                       (length head_data +
                        length
                          (firstn (valubytes - length head_data)
                             data))
                       (valu2list (fst (selN (DFData f) block_off valuset0)))),
                 vsmerge (selN (DFData f) block_off valuset0))) !!))
  -> tsupd_iter
  (tsupd ts pathname block_off
     (list2valu
        (firstn (length head_data)
           (valu2list (fst (selN (DFData f) block_off valuset0))) ++
         firstn (valubytes - length head_data) data ++
         skipn
           (length head_data +
            (valubytes - length head_data))
           (valu2list (fst (selN (DFData f) block_off valuset0)))),
     vsmerge (selN (DFData f) block_off valuset0))) pathname (block_off + 1)
  (combine
     (map list2valu
        (list_split_chunk
           (roundup
              (length data -
               (valubytes - length head_data)) valubytes /
            valubytes) valubytes
           (skipn (valubytes - length head_data) data ++
            skipn
              ((length data -
                (valubytes - length head_data)) mod valubytes)
              (valu2list
                 (fst
                    (selN (DFData f')
                    ( block_off + 1 +
                      (length data -
                       (valubytes - length head_data)) / valubytes)
                    valuset0))))))
     (map vsmerge
        (firstn
           (roundup
              (length data -
               (valubytes - length head_data)) valubytes /
            valubytes) (skipn (block_off + 1) (DFData f'))))) =
tsupd_iter ts pathname block_off
  (combine
     (map list2valu
        (list_split_chunk
           (roundup
              (length
                 (firstn (length head_data)
                    (valu2list (fst (selN (DFData f) block_off valuset0)))) +
               length data) valubytes / valubytes) valubytes
           (firstn (length head_data)
              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn
              (tpad_length
                 (length head_data + length data))
              (valu2list
                 (fst
                    (selN (DFData f)
                    ( block_off +
                      (length head_data + length data) /
                      valubytes ) valuset0))))))
     (map vsmerge
        (firstn
           (roundup
              (length
                 (firstn (length head_data)
                    (valu2list (fst (selN (DFData f) block_off valuset0)))) +
               length data) valubytes / valubytes)
           (skipn block_off (DFData f))))).
Proof.
(* original proof tokens: 958 *)

(* No more tactics to try *)
Admitted.

Definition read_from_block fsxp inum ams block_off byte_off read_length :=
      let^ (ms1, first_block) <- AFS.read_fblock fsxp inum block_off ams;
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(ms1, data_init).
Definition read_middle_blocks fsxp inum fms block_off num_of_full_blocks:=
let^ (ms, data) <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash Fm Ftop Fd ts ds fy sm data']
        Loopvar [ms' (data : list byte)]
        Invariant 
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL ms') sm hm *
        [[[ (ByFData fy) ::: Fd * arrayN (ptsto (V:= byteset)) (block_off * valubytes) data']]] *
        [[ data = map fst (firstn (i * valubytes) data')]] *
        [[ treeseq_in_ds Fm Ftop fsxp sm ms' ts ds ]] *
        [[ MSAlloc fms = MSAlloc ms' ]]
        OnCrash crash
        Begin (
          let^(fms', (list : list byte)) <- 
                read_from_block fsxp inum ms' (block_off + i) 0 valubytes;
          Ret ^(fms', data ++ list))%list Rof ^(fms, nil);
Ret ^(ms, data).
Definition read_last fsxp inum fms off n:=
If(lt_dec 0 n)
{
  let^ (ms1, data_last) <- read_from_block fsxp inum fms off 0 n;
  Ret ^(ms1, data_last)%list
}
else
{
  Ret ^(fms, nil)%list
}.
Definition read_middle fsxp inum fms block_off n:=
let num_of_full_blocks := (n / valubytes) in
let off_final := (block_off + num_of_full_blocks) in 
let len_final := n mod valubytes in 
If (lt_dec 0 num_of_full_blocks)
{
  let^ (ms1, data_middle) <- read_middle_blocks fsxp inum fms block_off num_of_full_blocks;
  If(lt_dec 0 len_final)
  {
    let^ (ms2, data_last) <- read_last fsxp inum ms1 off_final len_final;
    Ret ^(ms2, data_middle++data_last)%list
  }
  else
  {
    Ret ^(ms1, data_middle)%list
  }
}
else
{
  let^ (ms1, data_last) <- read_last fsxp inum fms off_final len_final;
  Ret ^(ms1, data_last)%list
}.
Definition read_first fsxp inum fms block_off byte_off n :=
If (lt_dec (valubytes - byte_off) n)
{
    let first_read_length := (valubytes - byte_off) in 
    let^ (ms1, data_first) <- read_from_block fsxp inum fms block_off byte_off first_read_length; 
  
    let block_off := S block_off in
    let len_remain := (n - first_read_length) in  
    let^ (ms2, data_rem) <- read_middle fsxp inum ms1 block_off len_remain;
    Ret ^(ms2, data_first++data_rem)%list
}
else
{
   let first_read_length := n in 
   let^ (ms1, data_first) <- read_from_block fsxp inum fms block_off byte_off first_read_length;   
   Ret ^(ms1, data_first)
}.
Definition read fsxp inum fms off len :=
If (lt_dec 0 len)                        
{                    
  let^ (ms1, fattr) <- AFS.file_get_attr fsxp inum fms;          
  let flen := # (INODE.ABytes fattr) in
  If (lt_dec off flen)                   
  {                             
      let block_off := off / valubytes in              
      let byte_off := off mod valubytes in          
      let^ (ms2, data) <- read_first fsxp inum ms1 block_off byte_off len;
      Ret ^(ms2, data)
  } 
  else                                                 
  {    
    Ret ^(ms1, nil)
  }
} 
else                                                   
{    
  Ret ^(fms, nil)
}.
Theorem read_from_block_ok: forall fsxp inum mscs block_off byte_off read_length,
    {< ds Fm Ftop Ftree pathname f fy Fd data ts sm,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:= byteset)) (block_off * valubytes + byte_off) data)) ]]] *
           [[ length data = read_length ]] *
           [[ 0 < length data ]] *
           [[ byte_off + read_length <= valubytes]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_from_block fsxp inum mscs block_off byte_off read_length.
Proof.
(* original proof tokens: 185 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (read_from_block _ _ _ _ _ _ ) _) => apply read_from_block_ok : prog.
Theorem read_middle_blocks_ok: forall fsxp inum mscs block_off num_of_full_blocks,
 {< ds ts sm Fm Ftop Ftree pathname f fy Fd data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (block_off * valubytes) data))]]] *
           [[ num_of_full_blocks > 0 ]] *
           [[ length data = mult num_of_full_blocks valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_middle_blocks fsxp inum mscs block_off num_of_full_blocks.
(* hint proof tokens: 252 *)
Proof.
  unfold read_middle_blocks; step.

  - step.
    rewrite <- plus_n_O.
    instantiate (1:= firstn valubytes (skipn (m * valubytes) data)).
    erewrite arrayN_split with (i:= m * valubytes).
    erewrite arrayN_split with (i:= valubytes)(a:=(skipn (m * valubytes) data)).
    rewrite Nat.mul_add_distr_r; cancel.
    length_rewrite_l.
    eapply length_le_middle; eauto.
    length_rewrite_l; auto.
    apply valubytes_ge_O.
    eapply length_le_middle; eauto. 

    step.
    apply map_app_firstn_skipn.

  - step.
    match goal with
    | [H: _ = num_of_full_blocks * valubytes |- _ ] => rewrite <- H
    end.
    rewrite firstn_exact; auto.
  
  - instantiate (1:= LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm).
    eapply LOG.idempred_hashmap_subset.
    exists l; auto.
    
  Unshelve.
  constructor.
Qed.
Hint Extern 1 ({{_}} Bind (read_middle_blocks _ _ _ _ _) _) => apply read_middle_blocks_ok : prog.
Theorem read_last_ok: forall fsxp inum mscs off n,
 {< ds ts sm  Fm Ftop Ftree pathname f fy Fd data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (off * valubytes) data))]]] *
           [[ length data = n ]] *
           [[ n < valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_last fsxp inum mscs off n.
(* hint proof tokens: 85 *)
Proof.
	unfold read_last; step.

  - step.
	  rewrite <- plus_n_O; cancel.
    step.
    
 - step.
   match goal with
   | [H: _ < _ -> False |- _ ] => 
                apply Nat.nlt_ge in H; inversion H as [Hx | ];
                apply length_nil in Hx; rewrite Hx; auto
   end.
Qed.
Hint Extern 1 ({{_}} Bind (read_last _ _ _ _ _) _) => apply read_last_ok : prog.
Theorem read_middle_ok: forall fsxp inum mscs off n,
 {< ds sm Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (off * valubytes) data))]]] *
           [[ length data = n ]] 
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_middle fsxp inum mscs off n.
(* hint proof tokens: 257 *)
Proof.
	unfold read_middle; step.
	
	- safestep.
	  5: instantiate (1:= firstn (length data / valubytes * valubytes) data).
	  eauto.
	  eauto.
	  eauto.
	  pred_apply.
    erewrite arrayN_split; cancel.
    length_rewrite_l.
    rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.

    step.
    + step.
        rewrite Nat.mul_add_distr_r.
	      rewrite arrayN_split with (i:= length data / valubytes * valubytes); cancel.
        length_rewrite_l.
        symmetry; rewrite Nat.mul_comm; apply Nat.mod_eq; auto.
        apply Nat.mod_upper_bound; auto.
	
	      step.
	      rewrite <- map_app.
	      rewrite firstn_skipn; auto.

	  + step.
        nlt_eq_0.
	      rewrite Rounding.mul_div; auto.
	      rewrite firstn_exact; auto.
	
	- step.
    rewrite_nlt; eauto.
	  rewrite Nat.mod_eq; auto.
	  rewrite_nlt; eauto.
	  rewrite <- mult_n_O.
	  apply minus_n_O.
    apply Nat.mod_upper_bound; auto.
    
    step.
Qed.
Hint Extern 1 ({{_}} Bind (read_middle _ _ _ _ _) _) => apply read_middle_ok : prog.
Theorem read_first_ok: forall fsxp inum mscs block_off byte_off n,
 {< ds sm Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off) data))]]] *
           [[ length data = n ]] *
           [[ n > 0 ]] *
           [[ byte_off < valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_first fsxp inum mscs block_off byte_off n.
(* hint proof tokens: 175 *)
Proof.
  unfold read_first; step.
  
  - safestep.
    5: instantiate (1:= firstn (valubytes - byte_off) data).
    eauto.
    eauto.
    eauto.
    pred_apply; erewrite arrayN_split; cancel.
    length_rewrite_l.
    length_rewrite_l.
  
    step.
    instantiate (1:= skipn (valubytes - byte_off) data).
    rewrite Nat.add_comm with (n:= valubytes).
    rewrite arrayN_split with (i:= valubytes - byte_off).
    rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; [cancel | lia].
    length_rewrite_l.
    
    step.
    rewrite <- map_app.
    rewrite firstn_skipn; auto.

  
  - step.
     step.
Qed.
Hint Extern 1 ({{_}} Bind (read_first _ _ _ _ _ _) _) => apply read_first_ok : prog.
Theorem read_ok: forall fsxp inum mscs off n,
 {< ds sm Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) off data))]]] *
           [[ (length data) = n ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read fsxp inum mscs off n.
Proof.
(* original proof tokens: 129 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (read _ _ _ _ _) _) => apply read_ok : prog.
Definition dwrite_to_block fsxp inum mscs block_off byte_off data :=
  let^ (ms1, block) <- AFS.read_fblock fsxp inum block_off mscs;
  let new_block := list2valu (firstn byte_off (valu2list block) ++ data ++ skipn (byte_off + length data) (valu2list block)) in
  ms2 <- AFS.update_fblock_d fsxp inum block_off new_block ms1;
  Ret ms2.
Definition dwrite_middle_blocks fsxp inum mscs block_off num_of_full_blocks data:=
   ms <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash Fm Ftop Ftree Ff pathname old_data f fy ds ts]
        Loopvar [ms']
        Invariant 
        exists ds' ts' sm' f' fy' bnl,
          let new_blocks := map list2valu (list_split_chunk 
                   i valubytes (firstn (i * valubytes) data)) in
                  
          let old_blocks := get_sublist (DFData f) block_off i in
        
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL ms') sm' hm *
          [[ treeseq_in_ds Fm Ftop fsxp sm' ms' ts' ds' ]] *
          [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
          [[ ts' = tsupd_iter ts pathname block_off
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
          [[ length bnl = i ]] *
          [[ treeseq_pred (treeseq_safe pathname (MSAlloc ms') (ts' !!)) ts' ]] *
          [[ (Ftree * pathname |-> File inum f')%pred  (dir2flatmem2 (TStree ts'!!)) ]] *
          [[ AByteFile.rep f' fy' ]] *
          [[[ (ByFData fy')::: (Ff * 
          arrayN (ptsto (V:= byteset)) (block_off * valubytes) 
            (merge_bs (firstn (i*valubytes) data) (firstn (i*valubytes) old_data)) *
          arrayN (ptsto(V:= byteset)) ((block_off + i) * valubytes) 
            (skipn (i * valubytes) old_data))]]] *
          [[ ByFAttr fy' = ByFAttr fy ]] *
          [[ MSAlloc mscs = MSAlloc ms' ]] *
          [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]]
        OnCrash crash
        Begin (
          let write_data := get_sublist data (i * valubytes) valubytes in
          fms' <- dwrite_to_block fsxp inum ms' (block_off + i) 0 write_data; 
          Ret (fms')) Rof ^(mscs);
  Ret (ms).
Definition dwrite_last fsxp inum mscs block_off data :=
  If (lt_dec 0 (length data))
  {
      ms1 <- dwrite_to_block fsxp inum mscs block_off 0 data;
      Ret (ms1)
  }
  else
  {
      Ret ^(mscs)
  }.
Definition dwrite_middle fsxp inum mscs block_off data:=
  let num_of_full_blocks := length data / valubytes in
  If(lt_dec 0 num_of_full_blocks)
  {
      let middle_data := firstn (num_of_full_blocks * valubytes) data in
      ms2 <- dwrite_middle_blocks fsxp inum mscs block_off num_of_full_blocks middle_data;
      
      let block_off := block_off + num_of_full_blocks in
      let remaining_data := skipn (num_of_full_blocks * valubytes) data in
      If(lt_dec 0 (length remaining_data))
      {
        ms3 <- dwrite_last fsxp inum (fst ms2) block_off remaining_data;
        Ret (ms3)
      }
      else
      {
        Ret (ms2)
      }
  }
  else
  {
      ms2 <- dwrite_last fsxp inum mscs block_off data;
      Ret (ms2)
  }.
Definition dwrite_first fsxp inum mscs block_off byte_off data :=
  let write_length := length data in
  If(le_dec write_length (valubytes - byte_off))
  {
      ms1 <- dwrite_to_block fsxp inum mscs block_off byte_off data;
      Ret (ms1)
  }
  else
  {
      let first_write_length := valubytes - byte_off in
      let first_data := firstn first_write_length data in
      
      ms1 <- dwrite_to_block fsxp inum mscs block_off byte_off first_data;
      
      let block_off := block_off + 1 in
      let remaining_data := skipn first_write_length data in
      ms2 <- dwrite_middle  fsxp inum (fst ms1) block_off remaining_data;
      Ret (ms2)
   }.
Definition dwrite fsxp inum mscs off data :=
  let write_length := length data in
  let block_off := off / valubytes in
  let byte_off := off mod valubytes in
  If (lt_dec 0 write_length)  
  { 
              ms1 <- dwrite_first fsxp inum mscs block_off byte_off data;
              Ret (ms1)
  }
  else
  {
    Ret ^(mscs)
  }.
Theorem dwrite_to_block_ok : forall fsxp inum block_off byte_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data head_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
           arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) head_data *
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off) old_data *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length old_data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data > 0 ]] *
  [[ byte_off + length data <= valubytes ]] *
  [[ byte_off = length head_data ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + byte_off + length data)) 
         (valubytes - (byte_off + length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bn fy' f' ds' ts' sm',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst old_blocks)) in
  let tail_pad := skipn (byte_off + length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (head_pad ++ data ++ tail_pad) in

  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
  [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ AByteFile.rep f' fy' ]] *
  [[[ (ByFData fy') ::: (Fd * 
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) (merge_bs (map fst head_data) head_data) *
          arrayN (ptsto (V:=byteset))
          (block_off * valubytes + byte_off) (merge_bs data old_data) *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length data) (merge_bs (map fst tail_data) tail_data))]]] *
  [[ ByFAttr fy = ByFAttr fy' ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]

XCRASH:hm'
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
  exists bn ds' ts' mscs' sm',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst old_blocks)) in
  let tail_pad := skipn (byte_off + length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (head_pad ++ data ++ tail_pad) in
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_to_block fsxp inum mscs block_off byte_off data.
(* hint proof tokens: 484 *)
Proof.
  unfold dwrite_to_block; step.

  remember (length head_data) as byte_off.
  apply addr_id.
  eapply inlen_bfile with (j:= byte_off); eauto.
  lia.
  instantiate (1:= old_data);
  lia.
  pred_apply; cancel.

  - step.
    remember (length head_data) as byte_off.
    apply addr_id.
    eapply inlen_bfile with (j:= byte_off); eauto.
    lia.
    instantiate (1:= old_data); lia.
    pred_apply; cancel.

    + unfold rep in *; split_hypothesis;
        safestep.
        eauto.
        eauto.
        eauto.
        eauto.
        eapply rep_modified_exists; eauto.

        eapply sep_star_modified_bytefile; eauto.
        match goal with | [H: (((_ ✶ _) ✶ _) ✶ _)%pred _ |- _] => apply arrayN_app_merge in H end.
        pred_apply; cancel.
        auto.
        match goal with | [H: _ = MSAlloc ?a |- context[MSAlloc ?a] ] => rewrite <- H end.
        match goal with | [H: forall _, _ -> treeseq_pred _ _ |- _ ] => apply H end.
        match goal with | [H: MSAlloc ?a = _ |- context[MSAlloc ?a] ] => rewrite H; auto end.

    + xcrash.
      or_r.
         match goal with | [H: (_, _) = _, H0: treeseq_in_ds _ _ _ _ _ (_, _) _ |- _ ] => 
          rewrite H in H0 end;
    match goal with | [H: MSAlloc ?a = _, H0: _ = MSAlloc ?a |- _ ] => 
          rewrite H in H0; clear H end;
    cancel;
    do 2 (rewrite crash_xform_exists_comm; cancel);
    rewrite crash_xform_exists_comm; unfold pimpl; intros.
    exists x0.
    apply crash_xform_exists_comm.
    eexists.
    pred_apply.
    repeat (rewrite crash_xform_sep_star_dist;
       rewrite crash_xform_lift_empty).
    safecancel;
    eauto.
    

  - xcrash.
Qed.
Hint Extern 1 ({{_}} Bind (dwrite_to_block _ _ _ _ _ _) _) => apply dwrite_to_block_ok : prog.
Theorem dwrite_middle_blocks_ok : forall fsxp inum block_off num_of_full_blocks data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data,
PRE:hm 
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
     [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
     [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
     [[ AByteFile.rep f fy ]] *
     [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:= byteset)) 
                          (block_off * valubytes) old_data)]]] *
     [[ length old_data = length data]] *
     [[ length data = mult num_of_full_blocks valubytes ]]
POST:hm' RET:^(mscs')  exists ts' fy' f' ds' sm' bnl,

    let new_blocks := map list2valu (list_split_chunk 
                   num_of_full_blocks valubytes data) in
                  
    let old_blocks := get_sublist (DFData f) block_off num_of_full_blocks in
    
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:= byteset)) (block_off * valubytes) (merge_bs data old_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     
     [[ length bnl =  num_of_full_blocks ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]]
     
XCRASH:hm'
  exists i ds' ts' mscs' sm' bnl,
  
    let new_blocks := map list2valu (list_split_chunk 
                   i valubytes (firstn (i * valubytes) data)) in
                  
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= num_of_full_blocks ]] *
   [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ ts' = tsupd_iter ts pathname block_off
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
   [[ length bnl = i ]] *
   [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_middle_blocks fsxp inum mscs block_off num_of_full_blocks data.
(* hint proof tokens: 647 *)
Proof.
    unfold dwrite_middle_blocks; safestep.
    3: instantiate (1:= nil).
    3: instantiate (1:= ds).
    9: rewrite <- plus_n_O.
    
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    pred_apply; cancel.
    eauto.
    eauto.
    eauto.

    
    - safestep.
      eauto.
      eauto.
      eauto.
      eauto.
      pred_apply.
      rewrite <- plus_n_O. 
      rewrite arrayN_split with (i:= valubytes)
      (a:= (skipn (length bnl * valubytes) old_data)) at 1.
      instantiate (1:= nil).
      instantiate (3:= nil).
      simpl; cancel.
      solve_ineq_dwrite_middle.
      solve_ineq_dwrite_middle.
      solve_ineq_dwrite_middle.
      auto.

      rewrite get_sublist_length at 2; auto;[| solve_ineq_dwrite_middle].
      replace (valubytes - valubytes) with 0 by lia.
      rewrite Nat.min_0_r; auto.

      + step.
          solve_dsupd_iter.
          solve_tsupd_iter.
          length_rewrite_l.
          solve_cancel_dwrite_middle block_off bnl.
          
          + subst; repeat xcrash_rewrite;
              xform_norm; cancel; xform_normr.
              * unfold pimpl; intros;
                 repeat apply sep_star_lift_apply'; 
                 [eauto | apply Nat.lt_le_incl; eauto | | | | | ].
                 all: eauto.
             * unfold pimpl; intros.
                repeat apply sep_star_lift_apply'.
                5: eauto.
                all: eauto.
                solve_dsupd_iter.
                solve_tsupd_iter.
                length_rewrite_l.

      - step;
        [rewrite <- H5;
        rewrite firstn_exact;
        rewrite <- H6;
        rewrite firstn_exact;
        rewrite skipn_exact;
        simpl; cancel
        | rewrite <- H5; rewrite firstn_exact; auto
        | rewrite <- H5; rewrite firstn_exact; auto].

    - instantiate (1:= LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) _ hm).
        unfold pimpl; intros m' Hy.
        apply sep_star_lift_apply in Hy as Hx.
        destruct Hx as [Hz  Hx0].
        clear Hz; pred_apply.
        split_hypothesis.

        subst; repeat xcrash_rewrite;
                   xform_norm; cancel; xform_normr.

        rewrite LOG.idempred_hashmap_subset; [| eauto].
        safecancel.
        4: eauto.
        instantiate (1:= 0); lia.
        instantiate (1:= nil).
        simpl; auto.
        simpl; auto.
        all: eauto.

        Unshelve.
        constructor.
 Qed.
Hint Extern 1 ({{_}} Bind (dwrite_middle_blocks _ _ _ _ _ _) _) => apply dwrite_middle_blocks_ok : prog.
Theorem dwrite_last_ok : forall fsxp inum block_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd *
           arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes) old_data *
           arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes + length old_data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data < valubytes ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + length data)) 
         (valubytes - length data) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bn fy' f' ds' ts' sm',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let tail_pad := skipn (length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (data ++ tail_pad) in
  ([[ length data = 0 ]] * 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm) \/
  (LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
  [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ AByteFile.rep f' fy' ]] *
  [[[ (ByFData fy') ::: (Fd * 
            arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes) (merge_bs data old_data) *
            arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes + length data) 
                  (merge_bs (map fst tail_data) tail_data))]]] *
  [[ ByFAttr fy = ByFAttr fy' ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]])

XCRASH:hm'
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
  exists bn ds' ts' mscs' sm',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let tail_pad := skipn (length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (data ++ tail_pad) in
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_last fsxp inum mscs block_off data.
Proof.
(* original proof tokens: 93 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (dwrite_last _ _ _ _ _) _) => apply dwrite_last_ok : prog.
Theorem dwrite_middle_ok : forall fsxp inum block_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data tail_data,
PRE:hm 
  let num_of_full_blocks := length data / valubytes in
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ tree_names_distinct (TStree ts !!) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
                        arrayN (ptsto (V:=byteset)) 
			                    (block_off * valubytes) old_data *
		                    arrayN (ptsto (V:=byteset)) 
			                    (block_off * valubytes + length old_data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data > 0 ]] * 
  [[ min (length (ByFData fy) - (block_off * valubytes + length data)) 
         (hpad_length (length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bnl fy' f' ds' ts' sm',
  let num_of_full_blocks := length data / valubytes in
  let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
  let tail_pad := skipn (length data mod valubytes) (valu2list (fst last_old_block))in
  let new_blocks :=  map list2valu 
            (list_split_chunk (roundup (length data) valubytes / valubytes) valubytes (data ++ tail_pad)) in
  let old_blocks := firstn (roundup (length data) valubytes / valubytes) (skipn block_off (DFData f)) in

  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * 
                            arrayN (ptsto (V:= byteset)) 
                              (block_off * valubytes) (merge_bs data old_data) *
                            arrayN (ptsto (V:=byteset)) 
			                        (block_off * valubytes + length data)
			                          (merge_bs (map fst tail_data) tail_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     
     [[ length bnl = (roundup (length data) valubytes / valubytes) ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]]
XCRASH:hm'
  exists i ds' ts' mscs' sm' bnl,
    let num_of_full_blocks := length data / valubytes in
    let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
    let tail_pad := skipn  (length data mod valubytes) (valu2list (fst last_old_block))in
    let new_blocks := map list2valu (list_split_chunk 
                   i valubytes (firstn (i * valubytes) (data ++ tail_pad))) in
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= (roundup (length data) valubytes / valubytes) ]] *
   [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ ts' = tsupd_iter ts pathname block_off
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
   [[ length bnl = i ]] *
   [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_middle fsxp inum mscs block_off data.
Proof.
(* original proof tokens: 2435 *)
unfold dwrite_middle; safestep.
eapply pimpl_ok2; [ | intros; simpl; apply pimpl_and_split; [ | apply pimpl_refl ]; rewrite LOG.notxn_idempred; cancel ]; eauto.
eapply pimpl_ok2; [ | intros; simpl; apply pimpl_and_split; [ | apply pimpl_refl ]; rewrite LOG.notxn_idempred; cancel ]; eauto.
eapply pimpl_ok2; [ | intros; simpl; apply pimpl_and_split; [ | apply pimpl_refl ]; rewrite LOG.notxn_idempred; cancel ]; eauto.
eapply pimpl_ok2; [ | intros; simpl; apply pimpl_and_split; [ | apply pimpl_refl ]; rewrite LOG.notxn_idempred; cancel ]; eauto.
eapply pimpl_ok2; [ | intros; simpl; apply pimpl_and_split; [ | apply pimpl_refl ]; rewrite LOG.notxn_idempred; cancel ]; eauto.
eapply pimpl_ok2; [ | intros; simpl; apply pimpl_and_split; [ | apply pimpl_refl ]; rewrite LOG.notxn_idempred; cancel ]; eauto.
eapply pimpl_ok2; [ | intros; simpl; apply pimpl_and_split; [ | apply pimpl_refl ]; rewrite LOG.notxn_idempred; cancel ]; eauto.
eapply pimpl_ok2; eauto.
(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (dwrite_middle _ _ _ _ _) _) => apply dwrite_middle_ok : prog.
Theorem dwrite_first_ok : forall fsxp inum block_off byte_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data head_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ tree_names_distinct (TStree ts !!) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
           arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) head_data *
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off) old_data *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data > 0 ]] *
  [[ byte_off < valubytes ]] *
  [[ byte_off = length head_data ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + byte_off + length data)) 
         (hpad_length (byte_off + length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bnl fy' f' ds' ts' sm',
  let first_old_block := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
  let num_of_full_blocks := (byte_off + length data) / valubytes in
  let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
  let tail_pad := skipn (tpad_length (byte_off + length data))
                    (valu2list (fst last_old_block)) in
  let new_blocks :=  map list2valu 
            (list_split_chunk (roundup (length head_pad + length data) valubytes / valubytes)
              valubytes (head_pad ++ data ++ tail_pad)) in
  let old_blocks := firstn (roundup (length head_pad + length data) valubytes / valubytes)
                      (skipn block_off (DFData f)) in

  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * 
                            arrayN (ptsto (V:=byteset))  
				                      (block_off * valubytes) 
			                          (merge_bs (map fst head_data) head_data) *
                            arrayN (ptsto (V:= byteset)) 
                              (block_off * valubytes + byte_off) (merge_bs data old_data) *
                            arrayN (ptsto (V:=byteset)) 
			                        (block_off * valubytes + byte_off + length data)
			                          (merge_bs (map fst tail_data) tail_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     
     [[ length bnl = roundup (length head_pad + length data) valubytes / valubytes ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]]
XCRASH:hm'
  exists i ds' ts' mscs' sm' bnl,
    let first_old_block := selN (DFData f) block_off valuset0 in
    let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
    let num_of_full_blocks := (byte_off + length data) / valubytes in
    let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
    let tail_pad := skipn  (tpad_length (byte_off + length data))
                      (valu2list (fst last_old_block)) in
    let new_blocks := map list2valu (list_split_chunk i valubytes 
                        (firstn (i * valubytes) (head_pad ++ data ++ tail_pad))) in
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= (roundup (length head_pad + length data) valubytes / valubytes) ]] *
  [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ ts' = tsupd_iter ts pathname block_off
                (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
  [[ length bnl = i ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_first fsxp inum mscs block_off byte_off data.
Proof.
(* original proof tokens: 4879 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (dwrite_first _ _ _ _ _ _) _) => apply dwrite_first_ok : prog.
Theorem dwrite_ok : forall fsxp inum off data mscs,
    let block_off := off / valubytes in
  let byte_off := off mod valubytes in
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data head_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ tree_names_distinct (TStree ts !!) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
           arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) head_data *
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off) old_data *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ byte_off < valubytes ]] *
  [[ byte_off = length head_data ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + byte_off + length data)) 
         (hpad_length (byte_off + length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bnl fy' f' ds' ts' sm',
  let first_old_block := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
  let num_of_full_blocks := (byte_off + length data) / valubytes in
  let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
  let tail_pad := skipn (tpad_length (byte_off + length data))
                    (valu2list (fst last_old_block)) in
  let new_blocks :=  map list2valu 
            (list_split_chunk (roundup (length head_pad + length data) valubytes / valubytes)
              valubytes (head_pad ++ data ++ tail_pad)) in
  let old_blocks := firstn (roundup (length head_pad + length data) valubytes / valubytes)
                      (skipn block_off (DFData f)) in
     ([[ length data = 0 ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm')
     \/
     ([[ length data > 0 ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * 
                            arrayN (ptsto (V:=byteset))  
				                      (block_off * valubytes) 
			                          (merge_bs (map fst head_data) head_data) *
                            arrayN (ptsto (V:= byteset)) 
                              (block_off * valubytes + byte_off) (merge_bs data old_data) *
                            arrayN (ptsto (V:=byteset)) 
			                        (block_off * valubytes + byte_off + length data)
			                          (merge_bs (map fst tail_data) tail_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     
     [[ length bnl = roundup (length head_pad + length data) valubytes / valubytes ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]])
XCRASH:hm'
  exists i ds' ts' mscs' sm' bnl,
    let first_old_block := selN (DFData f) block_off valuset0 in
    let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
    let num_of_full_blocks := (byte_off + length data) / valubytes in
    let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
    let tail_pad := skipn  (tpad_length (byte_off + length data))
                      (valu2list (fst last_old_block)) in
    let new_blocks := map list2valu (list_split_chunk i valubytes 
                        (firstn (i * valubytes) (head_pad ++ data ++ tail_pad))) in
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= (roundup (length head_pad + length data) valubytes / valubytes) ]] *
  [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ ts' = tsupd_iter ts pathname block_off
                (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
  [[ length bnl = i ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite fsxp inum mscs off data.
Proof.
(* original proof tokens: 34 *)
unfold dwrite; unfold rep; simpl; intros.
eapply pimpl_ok2; eauto; intros; simpl.
eapply pimpl_ok2; [ | eapply sep_star_lift_l; intros; eauto ]; intros; simpl; eauto.
eapply pimpl_ok2; [ | eapply sep_star_lift_l; [eapply pimpl_exists_l; intros|] ]; eauto.
eapply pimpl_ok2; [ | eapply sep_star_lift_l; [ eapply pimpl_exists_l; intros |] ]; eauto.
eapply pimpl_ok2; [ | eapply sep_star_lift_l; intros; eauto ]; intros; simpl; eauto.
eapply pimpl_ok2; [ | eapply sep_star_lift_l; intros; eauto ]; intros; simpl; eauto.
eapply pimpl_ok2; [ | eapply sep_star_lift_l; intros; eauto ]; intros; simpl; eauto.
eapply pimpl_ok2; [ | eapply sep_star_lift_l; intros; eauto ]; intros; simpl; eauto.
eapply pimpl_ok2; [ | eapply sep_star_lift_l; intros; eauto ]; intros; simpl; eauto.
eapply pimpl_ok2; [ | eapply sep_star_lift_l; [ eapply pimpl_exists_l; intros |] ]; eauto.
eapply pimpl_ok2; [ | eapply sep_star_lift_l; [eapply pimpl_exists_l; intros|] ]; eauto.
(* Reached max number of model calls *)
Admitted.

Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _ _) _) => apply dwrite_ok : prog.
Definition copydata fsxp src_inum tinum mscs :=
  let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
  let^ (mscs, data) <- read fsxp src_inum mscs 0 #(INODE.ABytes attr);
  let^ (mscs) <- dwrite fsxp tinum mscs 0 data;
  let^ (mscs) <- AFS.file_sync fsxp tinum mscs;   
  let^ (mscs, ok) <- AFS.file_set_attr fsxp tinum attr mscs;
  Ret ^(mscs, ok).
Theorem copydata_ok : forall fsxp srcinum tmppath tinum mscs,
{< ds ts sm Fm Ftop Ftree srcpath file tfile dstbase dstname dstfile fy tfy copy_data garbage,
PRE:hm
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
  [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
  [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep file fy ]] *
  [[ AByteFile.rep tfile tfy ]] *
  [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
  [[[ (ByFData tfy) ::: (arrayN (ptsto (V:= byteset)) 0 garbage) ]]] *
  [[ INODE.ABytes(ByFAttr fy) = INODE.ABytes (ByFAttr tfy) ]] *
  [[ length copy_data > 0 ]]
POST:hm' RET:^(mscs', r)
  exists ds' ts' sm',
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
   [[ MSAlloc mscs' = MSAlloc mscs ]] *
   [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
   [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
   (([[ isError r ]] *
          exists f', [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]])
         \/ ([[ r = OK tt ]] *
             exists tf' tfy', ([[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  tf' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]] *
            [[ AByteFile.rep tf' tfy' ]] *
            [[[ (ByFData tfy') ::: (arrayN (ptsto (V:= byteset)) 0 (map (fun x => (x, nil:list byte)) (map fst copy_data))) ]]] * [[ ByFAttr tfy' = ByFAttr fy]])))
XCRASH:hm'
  exists ds' ts' mscs' sm',
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
   [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
   [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
  >} copydata fsxp srcinum tinum mscs.
Proof.
(* original proof tokens: 1392 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (copydata _ _ _ _) _) => apply copydata_ok : prog.
Definition copy2temp fsxp src_inum tinum mscs :=
    let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
    let^ (mscs, ok) <- AFS.file_truncate fsxp tinum (roundup (# (INODE.ABytes attr)) valubytes / valubytes) mscs;
    match ok with
    | Err _ =>
        Ret ^(mscs, ok)
    | OK _ =>
        let^ (mscs, tattr) <- AFS.file_get_attr fsxp tinum mscs;
        let^ (mscs, ok) <-  AFS.file_set_attr fsxp tinum ((INODE.ABytes attr) , snd tattr) mscs;
        match ok with
        | OK _ =>    let^ (mscs, ok) <- copydata fsxp src_inum tinum mscs;
                            Ret ^(mscs, ok)
        | Err _ =>  
                            Ret ^(mscs, ok)
        end
    end.
Theorem copy2temp_ok : forall fsxp srcinum tinum mscs,
    {< Fm Ftop Ftree ds ts sm tmppath srcpath file tfile fy dstbase dstname dstfile copy_data,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[ AByteFile.rep file fy ]] *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
      [[ length (DFData tfile) <= length (DFData file) ]] *
      [[ length copy_data > 0 ]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts' sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
       (([[ isError r]] *
          exists f',
          [[ (tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!))) ]])
         \/ ([[ r = OK tt ]] *
             exists tf' tfy', ([[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  tf' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]] *
            [[ AByteFile.rep tf' tfy' ]] *
            [[[ (ByFData tfy') ::: (arrayN (ptsto (V:= byteset)) 0 (map (fun x => (x, nil:list byte)) (map fst copy_data))) ]]] * [[ ByFAttr tfy' = ByFAttr fy]])))
    XCRASH:hm'
     exists ds' ts' sm' mscs',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
    >} copy2temp fsxp srcinum tinum mscs.
Proof.
(* original proof tokens: 668 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.
Definition copy_and_rename fsxp src_inum tinum (dstbase:list string) (dstname:string) mscs :=
    let^ (mscs, ok) <- copy2temp fsxp src_inum tinum mscs;
    match ok with
      | Err _ =>
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        
        Ret ^(mscs, ok)
      | OK _ =>
        let^ (mscs, r) <- AFS.rename fsxp the_dnum [] temp_fn dstbase dstname mscs;
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        Ret ^(mscs, r)
    end.
Theorem copy_and_rename_ok : forall fsxp srcinum tinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree ds ts sm srcpath file tfile fy copy_data dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
     [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
       [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] * 
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[ AByteFile.rep file fy ]] *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
     [[ dirtree_inum (TStree ts!!) = the_dnum ]] *
     [[ length (DFData tfile) <= length (DFData file) ]] *
     [[ length copy_data > 0 ]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts' sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
      (([[ isError r ]] *
         (exists f' dfile,
         [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dfile) ts' ]] *
         [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                f' dstbase dstname dfile (dir2flatmem2 (TStree ts'!!)) ]])) \/
       ([[r = OK tt]] *
         (exists dfile dfy,
           [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dfile) ts' ]] *
           [[ tree_with_src Ftree srcpath [temp_fn] srcinum file dstbase dstname dfile  (dir2flatmem2 (TStree ts'!!)) ]] *
            [[AByteFile.rep dfile dfy ]] * 
            [[[ (ByFData dfy) ::: (arrayN (ptsto (V:= byteset)) 0 (map (fun x => (x, nil:list byte)) (map fst copy_data))) ]]] *
            [[ ByFAttr fy = ByFAttr dfy ]])))
    XCRASH:hm'
      exists mscs' ds' ts' sm',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       ((exists t, [[ ts' = (t, nil) ]] * 
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts']] )
       \/ (exists t ts'' dfile, [[ ts' = pushd t ts'' ]] * 
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dfile t ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts'' ]] ))
    >} copy_and_rename fsxp srcinum tinum dstbase dstname mscs.
Proof.
(* original proof tokens: 851 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (copy_and_rename _ _ _ _ _ _) _) => apply copy_and_rename_ok : prog.
