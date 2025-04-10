Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Lia.
Require Import Hashmap.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DiskSet.
Require Import DirTree.
Require Import Pred.
Require Import String.
Require Import List.
Require Import BFile.
Require Import Inode.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import AsyncDisk.
Require Import Array.
Require Import ListUtils.
Require Import DirTree.
Require Import DirSep.
Require Import Arith.
Require Import SepAuto.
Require Import Lia.
Require Import SuperBlock.
Require Import FSLayout.
Require Import AsyncFS.
Require Import Arith.
Require Import Errno.
Require Import List ListUtils.
Require Import GenSepAuto.
Require Import DirTreePath.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeNames.
Require Import DirTreeInodes.
Require Import DirTreeSafe.
Import DIRTREE.
Import ListNotations.
Module TREESEQ.
Notation MSLL := BFILE.MSLL.
Notation MSAlloc := BFILE.MSAlloc.
Record treeseq_one := mk_tree {
    TStree  : dirtree;
    TSilist : list INODE.inode;
    TSfree  : list addr * list addr
  }.
Definition treeseq_one_safe t1 t2 mscs :=
    dirtree_safe (TSilist t1) (BFILE.pick_balloc (TSfree t1) (MSAlloc mscs)) (TStree t1)
                         (TSilist t2) (BFILE.pick_balloc (TSfree t2) (MSAlloc mscs)) (TStree t2).
Theorem treeseq_one_safe_refl : forall t mscs,
    treeseq_one_safe t t mscs.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Theorem treeseq_one_safe_trans : forall t1 t2 t3 mscs,
    treeseq_one_safe t1 t2 mscs ->
    treeseq_one_safe t2 t3 mscs ->
    treeseq_one_safe t1 t3 mscs.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Definition treeseq := nelist treeseq_one.
Definition tree_rep F Ftop fsxp t :=
    (exists bfms sm,
     F * rep fsxp Ftop (TStree t) (TSilist t) (TSfree t) bfms sm)%pred.
Definition tree_rep_latest F Ftop fsxp sm t bfms :=
    (F * rep fsxp Ftop (TStree t) (TSilist t) (TSfree t) bfms sm)%pred.
Definition treeseq_in_ds F Ftop fsxp sm mscs (ts : treeseq) (ds : diskset) :=
    NEforall2
      (fun t d => tree_rep F Ftop fsxp t (list2nmem d) /\
                  treeseq_one_safe t (latest ts) mscs)
      ts ds /\
    tree_rep_latest F Ftop fsxp sm (ts!!) mscs (list2nmem ds!!).
Definition treeseq_pred (p : treeseq_one -> Prop) (ts : treeseq) := NEforall p ts.
Theorem treeseq_pred_pushd : forall (p : treeseq_one -> Prop) t ts,
    p t ->
    treeseq_pred p ts ->
    treeseq_pred p (pushd t ts).
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Theorem treeseq_in_ds_pushd : forall F Ftop fsxp sm mscs ts ds t mscs' d,
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    tree_rep_latest F Ftop fsxp sm t mscs' (list2nmem d) ->
    treeseq_one_safe (latest ts) t mscs ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ->
    treeseq_in_ds F Ftop fsxp sm mscs' (pushd t ts) (pushd d ds).
Proof.
(* skipped proof tokens: 107 *)
Admitted.
Definition treeseq_one_upd (t: treeseq_one) pathname off v :=
    match find_subtree pathname (TStree t) with
    | None => t
    | Some (TreeFile inum f) => mk_tree (update_subtree pathname 
                                  (TreeFile inum (mk_dirfile (updN (DFData f) off v) (DFAttr f))) (TStree t))
                           (TSilist t) (TSfree t)
    | Some (TreeDir inum d) => t
    end.
Definition tsupd (ts: treeseq) pathname off v :=
    d_map (fun t => treeseq_one_upd t pathname off v) ts.
Lemma tsupd_latest: forall (ts: treeseq) pathname off v,
    (tsupd ts pathname off v) !! = treeseq_one_upd (ts !!) pathname off v.
Proof.
(* original proof tokens: 24 *)
(* generated proof tokens: 23 *)

intros.
unfold tsupd.
rewrite d_map_latest.
reflexivity.
Qed.

Theorem treeseq_pred_impl : forall ts (p q : treeseq_one -> Prop),
    treeseq_pred p ts ->
    (forall t, p t -> q t) ->
    treeseq_pred q ts.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Definition treeseq_safe_fwd pathname (tnewest tolder : treeseq_one) :=
    forall inum off bn,
    (exists f, find_subtree pathname (TStree tolder) = Some (TreeFile inum f) /\
      BFILE.block_belong_to_file (TSilist tolder) bn inum off)
   ->
    (exists f', find_subtree pathname (TStree tnewest) = Some (TreeFile inum f') /\
     BFILE.block_belong_to_file (TSilist tnewest) bn inum off).
Definition treeseq_safe_bwd pathname flag (tnewest tolder : treeseq_one) :=
    forall inum off bn,
    (exists f', find_subtree pathname (TStree tnewest) = Some (TreeFile inum f') /\
     BFILE.block_belong_to_file (TSilist tnewest) bn inum off) ->
    ((exists f, find_subtree pathname (TStree tolder) = Some (TreeFile inum f) /\
      BFILE.block_belong_to_file (TSilist tolder) bn inum off) \/
     BFILE.block_is_unused (BFILE.pick_balloc (TSfree tolder) flag) bn).
Definition treeseq_safe pathname flag (tnewest tolder : treeseq_one) :=
    treeseq_safe_fwd pathname tnewest tolder /\
    treeseq_safe_bwd pathname flag tnewest tolder /\
    BFILE.ilist_safe (TSilist tolder)  (BFILE.pick_balloc (TSfree tolder)  flag)
                     (TSilist tnewest) (BFILE.pick_balloc (TSfree tnewest) flag).
Theorem treeseq_safe_trans: forall pathname flag t0 t1 t2,
    treeseq_safe pathname flag t0 t1 ->
    treeseq_safe pathname flag t1 t2 ->
    treeseq_safe pathname flag t0 t2.
Proof.
(* skipped proof tokens: 111 *)
Admitted.
Lemma tree_file_flist: forall F Ftop flist tree pathname inum f,
    find_subtree pathname tree = Some (TreeFile inum f) ->
    (F * tree_pred Ftop tree)%pred (list2nmem flist) ->
    tree_names_distinct tree ->
    exists c,
    selN flist inum BFILE.bfile0 = dirfile_to_bfile f c.
Proof.
(* skipped proof tokens: 69 *)
Admitted.
Ltac distinct_names :=
    match goal with
      [ H: (_ * rep _ _ ?tree _ _ _ _)%pred (list2nmem _) |- tree_names_distinct ?tree ] =>
        eapply rep_tree_names_distinct; eapply H
    end.
Ltac distinct_inodes :=
    match goal with
      [ H: (_ * rep _ _ ?tree _ _ _ _)%pred (list2nmem _) |- tree_inodes_distinct ?tree ] => 
        eapply rep_tree_inodes_distinct; eapply H
    end.
Lemma tree_file_length_ok: forall F Ftop fsxp ilist frees mscs sm d tree pathname off bn inum f,
      (F * rep Ftop fsxp tree ilist frees mscs sm)%pred d ->
      find_subtree pathname tree = Some (TreeFile inum f) ->
      BFILE.block_belong_to_file ilist bn inum off ->
      off < Datatypes.length (DFData f).
Proof.
(* skipped proof tokens: 272 *)
Admitted.
Lemma treeseq_in_ds_tree_pred_latest: forall Fm Ftop fsxp sm mscs ts ds,
   treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
   (Fm ✶ rep fsxp Ftop (TStree ts !!) (TSilist ts!!) (TSfree ts!!) mscs sm)%pred (list2nmem ds !!).
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Lemma treeseq_in_ds_tree_pred_nth: forall Fm Ftop fsxp mscs ts ds n sm,
   treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
   (exists bfms sm,
    Fm ✶ rep fsxp Ftop (TStree (nthd n ts)) (TSilist (nthd n ts)) (TSfree (nthd n ts)) bfms sm)%pred (list2nmem (nthd n ds)).
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_safe_refl : forall pathname flag tree,
   treeseq_safe pathname flag tree tree.
Proof.
(* skipped proof tokens: 44 *)
Admitted.
Lemma treeseq_safe_pushd: forall ts pathname flag tree',
    treeseq_pred (treeseq_safe pathname flag tree') ts ->
    treeseq_pred (treeseq_safe pathname flag tree') (pushd tree' ts).
Proof.
(* skipped proof tokens: 60 *)
Admitted.
Ltac distinct_names' :=
    repeat match goal with
      | [ H: treeseq_in_ds _ _ _ _ _ ?ts _ |- tree_names_distinct (TStree ?ts !!) ] =>
        eapply treeseq_in_ds_tree_pred_latest in H as Hpred;
        destruct_lift Hpred;
        eapply rep_tree_names_distinct; eassumption
      | [ H: treeseq_in_ds _ _ _ _ _ ?ts _ |- tree_names_distinct (TStree (nthd ?n ?ts)) ] => 
        eapply treeseq_in_ds_tree_pred_nth in H as Hpred;
        destruct_lift Hpred;
        eapply rep_tree_names_distinct; eassumption
    end.
Theorem treeseq_file_getattr_ok : forall fsxp inum mscs,
  {< ds sm ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] 
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
         [[ r = DFAttr f /\ MSAlloc mscs' = MSAlloc mscs ]] *
         [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]]
  CRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} AFS.file_get_attr fsxp inum mscs.
Proof.
(* skipped proof tokens: 126 *)
Admitted.
Theorem treeseq_lookup_ok: forall fsxp dnum fnlist mscs,
    {< ds sm ts Fm Ftop,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ dirtree_inum (TStree ts !!) = dnum ]] *
      [[ dirtree_isdir (TStree ts !!) = true ]]
    POST:hm' RET:^(mscs', r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[ (isError r /\ None = find_name fnlist (TStree ts !!)) \/
         (exists v, r = OK v /\ Some v = find_name fnlist (TStree ts !!))%type ]] *
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]]
    CRASH:hm'  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
     >} AFS.lookup fsxp dnum fnlist mscs.
Proof.
(* skipped proof tokens: 149 *)
Admitted.
Theorem treeseq_read_fblock_ok : forall fsxp inum off mscs,
    {< ds sm ts Fm Ftop Ftree pathname f Fd vs,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs', r)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
           [[ r = fst vs /\ MSAlloc mscs' = MSAlloc mscs ]] *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} AFS.read_fblock fsxp inum off mscs.
Proof.
(* skipped proof tokens: 131 *)
Admitted.
Lemma treeseq_block_belong_to_file: forall F Ftop fsxp t d pathname inum f off,
    tree_rep F Ftop fsxp t (list2nmem d) ->
    find_subtree pathname (TStree t) = Some (TreeFile inum f)  ->
    off < Datatypes.length (DFData f) ->
    exists bn, BFILE.block_belong_to_file (TSilist t) bn inum off.
Proof.
(* skipped proof tokens: 355 *)
Admitted.
Fact block_belong_to_file_bn_eq: forall tree bn bn0 inum off,
    BFILE.block_belong_to_file tree bn inum off ->
    BFILE.block_belong_to_file tree bn0 inum off ->
    bn = bn0.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma find_subtree_none_not_pathname_prefix_1 : forall t pn1 pn2 inum2 f2,
    find_subtree pn2 t = Some (TreeFile inum2 f2) ->
    find_subtree pn1 t = None ->
    ~ pathname_prefix pn1 pn2.
Proof.
(* skipped proof tokens: 38 *)
Admitted.
Lemma find_subtree_dir_not_pathname_prefix_2 : forall t pn1 pn2 inum f dnum d,
      pn1 <> pn2 ->
      find_subtree pn1 t = Some (TreeDir dnum d) ->
      find_subtree pn2 t = Some (TreeFile inum f) ->
      ~ pathname_prefix pn2 pn1.
Proof.
(* skipped proof tokens: 66 *)
Admitted.
Lemma find_subtree_file_not_pathname_prefix : forall t pn1 pn2 inum1 f1 inum2 f2,
    find_subtree pn1 t = Some (TreeFile inum1 f1) ->
    find_subtree pn2 t = Some (TreeFile inum2 f2) ->
    pn1 <> pn2 ->
    ~ pathname_prefix pn1 pn2.
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Lemma find_subtree_update_subtree_file_not_pathname_prefix_1 : forall t pn1 old pn2 inum1 f1 inum2 f2,
    find_subtree pn2 (update_subtree pn1 (TreeFile inum1 f1) t) = Some (TreeFile inum2 f2) ->
    find_subtree pn1 t = Some old ->
    pn1 <> pn2 ->
    ~ pathname_prefix pn1 pn2.
Proof.
(* skipped proof tokens: 56 *)
Admitted.
Lemma find_subtree_update_subtree_file_not_pathname_prefix_2 : forall t pn1 old pn2 inum1 f1 inum2 f2,
    find_subtree pn2 (update_subtree pn1 (TreeFile inum1 f1) t) = Some (TreeFile inum2 f2) ->
    find_subtree pn1 t = Some old ->
    pn1 <> pn2 ->
    ~ pathname_prefix pn2 pn1.
Proof.
(* skipped proof tokens: 128 *)
Admitted.
Lemma treeseq_safe_pushd_update_subtree : forall Ftree ts pathname ilist' f f' inum  mscs pathname' free2,
    let tree' := {|
        TStree := update_subtree pathname
                    (TreeFile inum f') 
                    (TStree ts !!);
        TSilist := ilist';
        TSfree := free2 |} in
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    Datatypes.length ilist' = Datatypes.length (TSilist ts!!) ->
    (Ftree * pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
    BFILE.ilist_safe (TSilist ts!!) (BFILE.pick_balloc (TSfree ts!!) (MSAlloc mscs))
                     ilist' (BFILE.pick_balloc free2 (MSAlloc mscs)) ->
    BFILE.treeseq_ilist_safe inum (TSilist ts!!) ilist' ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (pushd tree' ts) !!) (pushd tree' ts).
Proof.
(* skipped proof tokens: 998 *)
Admitted.
Ltac xcrash_solve :=
    repeat match goal with
           | [ H: forall _ _ _,  _ =p=> (?crash _) |- _ =p=> (?crash _) ] => eapply pimpl_trans; try apply H; cancel
           | [ |- crash_xform (LOG.rep _ _ _ _ _) =p=> _ ] => rewrite LOG.notxn_intact; cancel
           | [ H: crash_xform ?rc =p=> _ |- crash_xform ?rc =p=> _ ] => rewrite H; xform_norm
           end.
Lemma mscs_same_except_log_tree_rep_latest : forall mscs mscs' F Ftop fsxp t sm,
    BFILE.mscs_same_except_log mscs mscs' ->
    tree_rep_latest F Ftop fsxp sm t mscs =p=>
    tree_rep_latest F Ftop fsxp sm t mscs'.
Proof.
(* skipped proof tokens: 32 *)
Admitted.
Lemma mscs_parts_eq_tree_rep_latest : forall mscs mscs' F Ftop fsxp t sm,
    MSCache mscs' = MSCache mscs ->
    MSICache mscs' = MSICache mscs ->
    MSAllocC mscs' = MSAllocC mscs ->
    MSIAllocC mscs' = MSIAllocC mscs ->
    MSDBlocks mscs' = MSDBlocks mscs ->
    tree_rep_latest F Ftop fsxp t sm mscs =p=>
    tree_rep_latest F Ftop fsxp t sm mscs'.
Proof.
(* skipped proof tokens: 49 *)
Admitted.
Lemma mscs_same_except_log_treeseq_one_safe : forall mscs mscs' t t',
    BFILE.mscs_same_except_log mscs mscs' ->
    treeseq_one_safe t t' mscs ->
    treeseq_one_safe t t' mscs'.
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Lemma mscs_same_except_log_rep_treeseq_in_ds : forall F Ftop fsxp sm mscs mscs' ts ds,
    BFILE.mscs_same_except_log mscs mscs' ->
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    treeseq_in_ds F Ftop fsxp sm mscs' ts ds.
Proof.
(* skipped proof tokens: 73 *)
Admitted.
Lemma treeseq_in_ds_eq: forall Fm Ftop fsxp sm mscs a ts ds,
    BFILE.mscs_same_except_log a mscs ->
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds <->
    treeseq_in_ds Fm Ftop fsxp sm a ts ds.
Proof.
(* skipped proof tokens: 44 *)
Admitted.
Lemma treeseq_in_ds_mscs' : forall Fm Ftop fsxp sm mscs mscs' ts ds,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    (Fm * rep fsxp Ftop (TStree ts !!) (TSilist ts !!) (TSfree ts !!) mscs' sm)%pred (list2nmem ds !!) ->
    MSAlloc mscs = MSAlloc mscs' ->
    treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds.
Proof.
(* skipped proof tokens: 59 *)
Admitted.
Theorem treeseq_file_set_attr_ok : forall fsxp inum attr mscs,
  {< ds sm ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
     [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
     [[ (Ftree * pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts!!)) ]] 
  POST:hm' RET:^(mscs', ok)
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] \/
      [[ ok = OK tt  ]] * exists d ds' ts' tree' ilist' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm hm' *
        [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' (TSfree ts !!) mscs' sm) ]]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts!!) ]] *
        [[ ts' = pushd (mk_tree tree' ilist' (TSfree ts !!)) ts ]] *
        [[ f' = mk_dirfile (DFData f) attr ]] *
        [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]])
   XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists d ds' ts' mscs' tree' ilist' f',
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
         [[ MSAlloc mscs' = MSAlloc mscs ]] *
         [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds' ]] *
         [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
         [[ ds' = pushd d ds ]] *
         [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' (TSfree ts !!) mscs' sm) ]]] *
         [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts!!) ]] *
         [[ ts' = pushd (mk_tree tree' ilist' (TSfree ts !!)) ts ]] *
         [[ f' = mk_dirfile (DFData f) attr ]] *
         [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]]
    >} AFS.file_set_attr fsxp inum attr mscs.
Proof.
(* skipped proof tokens: 532 *)
Admitted.
Theorem treeseq_file_grow_ok : forall fsxp inum newlen mscs,
  {< ds sm ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
     [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
     [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
     [[ newlen >= Datatypes.length (DFData f) ]]
  POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ isError ok ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] \/
      [[ ok = OK tt ]] * exists d ds' ts' ilist' frees' tree' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm hm' *
        [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)]]] *
        [[ f' = mk_dirfile (setlen (DFData f) newlen ($0, nil)) (DFAttr f) ]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]])
  XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists d ds' sm' ts' mscs' tree' ilist' f' frees',
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
         [[ MSAlloc mscs' = MSAlloc mscs ]] *
         [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
         [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
         [[ ds' = pushd d ds ]] *
         [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
         [[ f' = mk_dirfile (setlen (DFData f) newlen ($0, nil)) (DFAttr f) ]] *
         [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts !!) ]] *
         [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
         [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]]
  >} AFS.file_truncate fsxp inum newlen mscs.
Proof.
(* skipped proof tokens: 563 *)
Admitted.
Lemma block_is_unused_xor_belong_to_file : forall F Ftop fsxp t m flag bn inum off,
    tree_rep F Ftop fsxp t m ->
    BFILE.block_is_unused (BFILE.pick_balloc (TSfree t) flag) bn ->
    BFILE.block_belong_to_file (TSilist t) bn inum off ->
    False.
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Lemma tree_rep_nth_upd: forall F Ftop fsxp sm mscs ts ds n pathname bn off v inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    tree_rep F Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    tree_rep F Ftop fsxp (treeseq_one_upd (nthd n ts) pathname off v) (list2nmem (nthd n ds) ⟦ bn := v ⟧).
Proof.
(* skipped proof tokens: 510 *)
Admitted.
Lemma tree_rep_latest_upd: forall F Ftop fsxp sm mscs ts ds pathname bn off v inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    tree_rep_latest F Ftop fsxp sm (ts !!) mscs (list2nmem (ds !!)) ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    tree_rep_latest F Ftop fsxp sm (treeseq_one_upd (ts !!) pathname off v) mscs (list2nmem (ds !!) ⟦ bn := v ⟧).
Proof.
(* skipped proof tokens: 468 *)
Admitted.
Lemma treeseq_one_upd_alternative : forall t pathname off v,
    treeseq_one_upd t pathname off v =
    mk_tree (match find_subtree pathname (TStree t) with
             | Some (TreeFile inum f) => update_subtree pathname (TreeFile inum (mk_dirfile (updN (DFData f) off v) (DFAttr f))) (TStree t)
             | Some (TreeDir _ _) => TStree t
             | None => TStree t
             end) (TSilist t) (TSfree t).
Proof.
(* skipped proof tokens: 53 *)
Admitted.
Lemma treeseq_one_safe_dsupd_1 : forall tolder tnewest mscs mscs' pathname off v inum f,
    tree_names_distinct (TStree tolder) ->
    treeseq_one_safe tolder tnewest mscs ->
    find_subtree pathname (TStree tnewest) = Some (TreeFile inum f) ->
    MSAlloc mscs' = MSAlloc mscs ->
    treeseq_one_safe (treeseq_one_upd tolder pathname off v) tnewest mscs'.
Proof.
(* skipped proof tokens: 343 *)
Admitted.
Lemma treeseq_one_safe_dsupd_2 : forall tolder tnewest mscs mscs' pathname off v inum f,
    tree_names_distinct (TStree tnewest) ->
    treeseq_one_safe tolder tnewest mscs ->
    find_subtree pathname (TStree tnewest) = Some (TreeFile inum f) ->
    MSAlloc mscs' = MSAlloc mscs ->
    treeseq_one_safe tolder (treeseq_one_upd tnewest pathname off v) mscs'.
Proof.
(* skipped proof tokens: 174 *)
Admitted.
Lemma treeseq_one_safe_dsupd : forall tolder tnewest mscs mscs' pathname off v inum f,
    tree_names_distinct (TStree tolder) ->
    tree_names_distinct (TStree tnewest) ->
    treeseq_one_safe tolder tnewest mscs ->
    find_subtree pathname (TStree tnewest) = Some (TreeFile inum f) ->
    MSAlloc mscs' = MSAlloc mscs ->
    treeseq_one_safe (treeseq_one_upd tolder pathname off v)
      (treeseq_one_upd tnewest pathname off v) mscs'.
Proof.
(* skipped proof tokens: 65 *)
Admitted.
Theorem treeseq_in_ds_upd : forall F Ftop fsxp sm mscs ts ds sm' mscs' pathname bn off v inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    treeseq_pred (treeseq_safe pathname  (BFILE.MSAlloc mscs) (ts !!)) ts ->
    MSAlloc mscs = MSAlloc mscs' ->
    (F * rep fsxp Ftop (TStree (tsupd ts pathname off v) !!) (TSilist ts !!) (TSfree ts !!) mscs' sm')%pred
      (list2nmem (dsupd ds bn v) !!) ->
    treeseq_in_ds F Ftop fsxp sm' mscs' (tsupd ts pathname off v) (dsupd ds bn v).
Proof.
(* original proof tokens: 226 *)
intros.
unfold tsupd.
(* No more tactics to try *)
Admitted.

Theorem treeseq_in_ds_upd' : forall F Ftop fsxp sm mscs ts ds pathname bn off v inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    treeseq_pred (treeseq_safe pathname  (BFILE.MSAlloc mscs) (ts !!)) ts ->
    treeseq_in_ds F Ftop fsxp sm mscs (tsupd ts pathname off v) (dsupd ds bn v).
Proof.
(* skipped proof tokens: 188 *)
Admitted.
Lemma seq_upd_safe_upd_fwd_ne: forall pathname pathname' inum n ts off v f mscs,
    pathname' <> pathname ->
    tree_names_distinct (TStree (nthd n ts)) ->
    tree_names_distinct (TStree ts !!) ->
     find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    treeseq_safe_fwd pathname ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname (MSAlloc mscs) ts !! (nthd n ts) ->
    treeseq_safe_fwd pathname' ts !! (nthd n ts) ->
    treeseq_safe_fwd pathname'
      {|
      TStree := update_subtree pathname
                  (TreeFile inum
                     {|
                     DFData := (DFData f) ⟦ off := v ⟧;
                     DFAttr := DFAttr f |}) (TStree ts !!);
      TSilist := TSilist ts !!;
      TSfree := TSfree ts !! |}
      {|
      TStree := match find_subtree pathname (TStree (nthd n ts)) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0
                         {|
                         DFData := (DFData f0) ⟦ off := v ⟧;
                         DFAttr := DFAttr f0 |}) (TStree (nthd n ts))
                | Some (TreeDir _ _) => TStree (nthd n ts)
                | None => TStree (nthd n ts)
                end;
      TSilist := TSilist (nthd n ts);
      TSfree := TSfree (nthd n ts) |}.
Proof.
(* skipped proof tokens: 450 *)
Admitted.
Lemma seq_upd_safe_upd_bwd_ne: forall pathname pathname' inum n ts off v f mscs,
    pathname' <> pathname ->
    tree_names_distinct (TStree (nthd n ts)) ->
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    treeseq_safe_fwd pathname ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname (MSAlloc mscs) ts !! (nthd n ts) ->
    treeseq_safe_fwd pathname' ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname' (MSAlloc mscs) ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname' (MSAlloc mscs)
      {|
      TStree := update_subtree pathname
                  (TreeFile inum
                     {|
                     DFData := (DFData f) ⟦ off := v ⟧;
                     DFAttr := DFAttr f |}) (TStree ts !!);
      TSilist := TSilist ts !!;
      TSfree := TSfree ts !! |}
      {|
      TStree := match find_subtree pathname (TStree (nthd n ts)) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0
                         {|
                         DFData := (DFData f0) ⟦ off := v ⟧;
                         DFAttr := DFAttr f0 |}) (TStree (nthd n ts))
                | Some (TreeDir _ _) => TStree (nthd n ts)
                | None => TStree (nthd n ts)
                end;
      TSilist := TSilist (nthd n ts);
      TSfree := TSfree (nthd n ts) |}.
Proof.
(* skipped proof tokens: 466 *)
Admitted.
Lemma treeseq_upd_safe_upd: forall Fm fsxp Ftop mscs mscs' Ftree sm ts ds n pathname pathname' f f' off v inum bn,
    (Fm ✶ rep fsxp Ftop (update_subtree pathname (TreeFile inum f') (TStree ts !!)) (TSilist ts !!)
         (fst (TSfree ts !!), snd (TSfree ts !!)) mscs' sm)%pred (list2nmem (dsupd ds bn v) !!) ->
    (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) -> 
    MSAlloc mscs = MSAlloc mscs' ->
    True ->
    BFILE.block_belong_to_file (TSilist ts !!) bn inum off ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
    treeseq_safe pathname (MSAlloc mscs) ts !! (nthd n ts) ->
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    tree_rep Fm Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_safe pathname' (MSAlloc mscs)
      (treeseq_one_upd ts !! pathname off v)
      (treeseq_one_upd (nthd n ts) pathname off v).
Proof.
(* skipped proof tokens: 900 *)
Admitted.
Theorem treeseq_update_fblock_d_ok : forall fsxp inum off v mscs,
    {< ds sm ts Fm Ftop Ftree pathname f Fd vs,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs')
      exists ts' f' ds' sm' bn,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
       [[ ts' = tsupd ts pathname off (v, vsmerge vs) ]] *
       [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
       [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]] *
       [[[ (DFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
       [[ DFAttr f' = DFAttr f ]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists ds' ts' mscs' sm' bn,
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
         [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
         [[ MSAlloc mscs' = MSAlloc mscs ]] *
         [[ ts' = tsupd ts pathname off (v, vsmerge vs) ]] *
         [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
         [[ BFILE.block_belong_to_file (TSilist ts !!) bn inum off ]]
   >} AFS.update_fblock_d fsxp inum off v mscs.
Proof.
(* skipped proof tokens: 889 *)
Admitted.
Definition treeseq_one_file_sync (t: treeseq_one) pathname :=
      match find_subtree pathname (TStree t) with
      | None => t
      | Some (TreeFile inum f) => 
        mk_tree (update_subtree pathname (TreeFile inum (synced_dirfile f)) (TStree t)) (TSilist t) (TSfree t)
      | Some (TreeDir _ _) => t
      end.
Definition ts_file_sync pathname (ts: treeseq) :=
    d_map (fun t => treeseq_one_file_sync t pathname) ts.
Fixpoint synced_up_to_n n (vsl : list valuset) : list valuset :=
    match n with
    | O => vsl
    | S n' =>
      match vsl with
      | nil => nil
      | vs :: vsl' => (fst vs, nil) :: (synced_up_to_n n' vsl')
      end
    end.
Theorem synced_list_up_to_n : forall vsl,
    synced_list (map fst vsl) = synced_up_to_n (length vsl) vsl.
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Lemma length_synced_up_to_n : forall n vsl,
    length vsl = length (synced_up_to_n n vsl).
Proof.
(* skipped proof tokens: 32 *)
Admitted.
Lemma synced_up_to_n_nil : forall n, synced_up_to_n n nil = nil.
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Lemma synced_up_to_n_too_long : forall vsl n,
    n >= Datatypes.length vsl ->
    synced_up_to_n n vsl = synced_up_to_n (Datatypes.length vsl) vsl.
Proof.
(* skipped proof tokens: 53 *)
Admitted.
Lemma cons_synced_up_to_n' : forall synclen d l default,
    synclen <= Datatypes.length l ->
    (fst d, []) :: synced_up_to_n synclen l =
    synced_up_to_n synclen (d :: l) ⟦ synclen := (fst (selN (d :: l) synclen default), nil) ⟧.
Proof.
(* skipped proof tokens: 59 *)
Admitted.
Lemma cons_synced_up_to_n : forall synclen d l default,
    (fst d, []) :: synced_up_to_n synclen l =
    synced_up_to_n synclen (d :: l) ⟦ synclen := (fst (selN (d :: l) synclen default), nil) ⟧.
Proof.
(* skipped proof tokens: 96 *)
Admitted.
Fixpoint synced_file_alt_helper f off :=
    match off with
    | O => f
    | S off' =>
      let f' := mk_dirfile (updN (DFData f) off' (fst (selN (DFData f) off' ($0, nil)), nil)) (DFAttr f) in
      synced_file_alt_helper f' off'
    end.
Fixpoint synced_file_alt_helper2 f off {struct off} :=
    match off with
    | O => f
    | S off' =>
      let f' := synced_file_alt_helper2 f off' in
      mk_dirfile (updN (DFData f') off' (fst (selN (DFData f') off' ($0, nil)), nil)) (DFAttr f')
    end.
Lemma synced_file_alt_helper2_oob : forall off f off' v,
    let f' := synced_file_alt_helper f off in
    off' >= off ->
    (mk_dirfile (updN (DFData f') off' v) (DFAttr f')) =
    synced_file_alt_helper (mk_dirfile (updN (DFData f) off' v) (DFAttr f)) off.
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Lemma synced_file_alt_helper_selN_oob : forall off f off' default,
    off' >= off ->
    selN (DFData (synced_file_alt_helper f off)) off' default =
    selN (DFData f) off' default.
Proof.
(* skipped proof tokens: 41 *)
Admitted.
Theorem synced_file_alt_helper_helper2_equiv : forall off f,
    synced_file_alt_helper f off = synced_file_alt_helper2 f off.
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Lemma synced_file_alt_helper2_selN_oob : forall off f off' default,
    off' >= off ->
    selN (DFData (synced_file_alt_helper2 f off)) off' default =
    selN (DFData f) off' default.
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Lemma synced_file_alt_helper2_length : forall off f,
    Datatypes.length (DFData (synced_file_alt_helper2 f off)) = Datatypes.length (DFData f).
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Definition synced_file_alt f :=
    synced_file_alt_helper f (Datatypes.length (DFData f)).
Theorem synced_file_alt_equiv : forall f,
    synced_dirfile f = synced_file_alt f.
Proof.
(* skipped proof tokens: 148 *)
Admitted.
Lemma treeseq_one_upd_noop : forall t pathname off v inum f def,
    tree_names_distinct (TStree t) ->
    find_subtree pathname (TStree t) = Some (TreeFile inum f) ->
    off < Datatypes.length (DFData f) ->
    selN (DFData f) off def = v ->
    t = treeseq_one_upd t pathname off v.
Proof.
(* skipped proof tokens: 86 *)
Admitted.
Fixpoint treeseq_one_file_sync_alt_helper (t : treeseq_one) (pathname : list string) off fdata :=
    match off with
    | O => t
    | S off' =>
      let t' := treeseq_one_upd t pathname off' (selN fdata off' $0, nil) in
      treeseq_one_file_sync_alt_helper t' pathname off' fdata
    end.
Definition treeseq_one_file_sync_alt (t : treeseq_one) (pathname : list string) :=
    match find_subtree pathname (TStree t) with
    | None => t
    | Some (TreeDir _ _) => t
    | Some (TreeFile inum f) =>
      treeseq_one_file_sync_alt_helper t pathname (length (DFData f)) (map fst (DFData f))
    end.
Lemma treeseq_one_file_sync_alt_equiv : forall t pathname,
    tree_names_distinct (TStree t) ->
    treeseq_one_file_sync t pathname = treeseq_one_file_sync_alt t pathname.
Proof.
(* skipped proof tokens: 407 *)
Admitted.
Lemma treeseq_one_file_sync_alt_equiv_d_map : forall pathname ts,
    NEforall (fun t => tree_names_distinct (TStree t)) ts ->
    d_map (fun t => treeseq_one_file_sync t pathname) ts =
    d_map (fun t => treeseq_one_file_sync_alt t pathname) ts.
Proof.
(* skipped proof tokens: 87 *)
Admitted.
Theorem dirtree_update_safe_pathname_vssync_vecs_file:
    forall pathname f tree fsxp F F0 ilist freeblocks mscs sm inum m al,
    let tree_newest := update_subtree pathname (TreeFile inum (synced_dirfile f)) tree in
    find_subtree pathname tree = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (forall i, i < length al -> BFILE.block_belong_to_file ilist (selN al i 0) inum i) ->
    (F0 * rep fsxp F tree ilist freeblocks mscs sm)%pred (list2nmem m) ->
    (F0 * rep fsxp F tree_newest ilist freeblocks mscs sm)%pred (list2nmem (vssync_vecs m al)).
Proof.
(* skipped proof tokens: 630 *)
Admitted.
Lemma block_belong_to_file_off_ok : forall Fm Ftop fsxp sm mscs ts t ds inum off pathname f,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    d_in t ts ->
    find_subtree pathname (TStree t) = Some (TreeFile inum f) ->
    off < Datatypes.length (DFData f) ->
    BFILE.block_belong_to_file
      (TSilist t)
      (wordToNat (selN (INODE.IBlocks (selN (TSilist t) inum INODE.inode0)) off $0))
      inum off.
Proof.
(* skipped proof tokens: 139 *)
Admitted.
Lemma block_belong_to_file_bfdata_length : forall Fm Ftop fsxp mscs sm ts ds inum off t pathname f bn,
    treeseq_in_ds Fm Ftop fsxp mscs sm ts ds ->
    d_in t ts ->
    find_subtree pathname (TStree t) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist t) bn inum off ->
    off < Datatypes.length (DFData f).
Proof.
(* skipped proof tokens: 235 *)
Admitted.
Lemma treeseq_safe_fwd_length : forall Fm Ftop fsxp mscs sm ts ds n inum inum' f b pathname,
    treeseq_in_ds Fm Ftop fsxp mscs sm ts ds ->
    treeseq_safe_fwd pathname (ts !!) (nthd n ts) ->
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    find_subtree pathname (TStree (nthd n ts)) = Some (TreeFile inum' b) ->
    length (DFData b) <= length (DFData f).
Proof.
(* skipped proof tokens: 122 *)
Admitted.
Lemma tree_rep_nth_file_sync: forall Fm Ftop fsxp mscs sm ds ts n al pathname inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    tree_rep Fm Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    tree_rep Fm Ftop fsxp (treeseq_one_file_sync (nthd n ts) pathname) (list2nmem (vssync_vecs (nthd n ds) al)).
Proof.
(* skipped proof tokens: 1282 *)
Admitted.
Lemma tree_rep_latest_file_sync: forall Fm Ftop fsxp mscs sm ds ts al pathname inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    tree_rep_latest Fm Ftop fsxp sm (ts !!) mscs (list2nmem (ds !!)) ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    tree_rep_latest Fm Ftop fsxp sm (treeseq_one_file_sync (ts !!) pathname) mscs (list2nmem (vssync_vecs (ds !!) al)).
Proof.
(* skipped proof tokens: 1167 *)
Admitted.
Lemma tree_safe_file_sync_1 : forall Fm Ftop fsxp mscs sm ds ts mscs' pathname,
    (exists inum f, find_subtree pathname (TStree ts !!) = Some (TreeFile inum f)) ->
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs -> 
    treeseq_one_safe (ts !!) (treeseq_one_file_sync (ts !!) pathname) mscs'.
Proof.
(* skipped proof tokens: 271 *)
Admitted.
Lemma treeseq_in_ds_one_safe : forall Fm Ftop fsxp mscs mscs' sm ts ds n,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    MSAlloc mscs' = MSAlloc mscs ->
    treeseq_one_safe (nthd n ts) ts !! mscs'.
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Lemma tree_safe_file_sync_2 : forall Fm Ftop fsxp mscs sm ds ts mscs' n pathname,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs -> 
    treeseq_one_safe (treeseq_one_file_sync (nthd n ts) pathname) (ts !!) mscs'.
Proof.
(* skipped proof tokens: 404 *)
Admitted.
Lemma tree_safe_file_sync: forall Fm Ftop fsxp mscs sm ds ts mscs' n al pathname inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (length al = length (DFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs -> 
    treeseq_one_safe (treeseq_one_file_sync (nthd n ts) pathname) 
     (d_map (fun t : treeseq_one => treeseq_one_file_sync t pathname) ts) !! mscs'.
Proof.
(* skipped proof tokens: 52 *)
Admitted.
Lemma treeseq_in_ds_file_sync: forall  Fm Ftop fsxp mscs mscs' sm sm' ds ts al pathname inum  f,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (length al = length (DFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    MSAlloc mscs = MSAlloc mscs' ->
    (Fm * rep fsxp Ftop (TStree (ts_file_sync pathname ts) !!) (TSilist ts !!) (TSfree ts !!) mscs' sm')%pred
        (list2nmem (dssync_vecs ds al) !!) ->
    treeseq_in_ds Fm Ftop fsxp sm' mscs' (ts_file_sync pathname ts) (dssync_vecs ds al).
Proof.
(* skipped proof tokens: 193 *)
Admitted.
Lemma treeseq_in_ds_file_sync' : forall  Fm Ftop fsxp sm mscs ds ts al pathname inum  f,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (length al = length (DFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp sm mscs (ts_file_sync pathname ts) (dssync_vecs ds al).
Proof.
(* skipped proof tokens: 170 *)
Admitted.
Lemma treeseq_one_file_sync_alternative : forall t pathname,
    treeseq_one_file_sync t pathname =
    mk_tree (match find_subtree pathname (TStree t) with
             | Some (TreeFile inum f) => update_subtree pathname (TreeFile inum (synced_dirfile f)) (TStree t)
             | Some (TreeDir _ _) => TStree t
             | None => TStree t
             end) (TSilist t) (TSfree t).
Proof.
(* original proof tokens: 53 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_safe_fwd_ne: forall pathname pathname' n ts inum f,
    pathname <> pathname' ->
    tree_names_distinct (TStree ts !!) ->
    tree_names_distinct (TStree (nthd n ts)) -> 
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    treeseq_safe_fwd pathname ts !! (nthd n ts) ->
    treeseq_safe_fwd pathname' ts !! (nthd n ts) ->
    treeseq_safe_fwd pathname'
      {|
      TStree := match find_subtree pathname (TStree ts !!) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0 (synced_dirfile f0)) (TStree ts !!)
                | Some (TreeDir _ _) => TStree ts !!
                | None => TStree ts !!
                end;
      TSilist := TSilist ts !!;
      TSfree := TSfree ts !! |}
      {|
      TStree := match find_subtree pathname (TStree (nthd n ts)) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0 (synced_dirfile f0))
                      (TStree (nthd n ts))
                | Some (TreeDir _ _) => TStree (nthd n ts)
                | None => TStree (nthd n ts)
                end;
      TSilist := TSilist (nthd n ts);
      TSfree := TSfree (nthd n ts) |}.
Proof.
(* skipped proof tokens: 313 *)
Admitted.
Lemma treeseq_safe_bwd_ne: forall pathname pathname' ts n inum f mscs,
    pathname <> pathname' ->
    tree_names_distinct (TStree ts !!) ->
    tree_names_distinct (TStree (nthd n ts)) -> 
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    treeseq_safe_bwd pathname (MSAlloc mscs) ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname' (MSAlloc mscs) ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname' (MSAlloc mscs)
      {|
      TStree := match find_subtree pathname (TStree ts !!) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0 (synced_dirfile f0)) (TStree ts !!)
                | Some (TreeDir _ _) => TStree ts !!
                | None => TStree ts !!
                end;
      TSilist := TSilist ts !!;
      TSfree := TSfree ts !! |}
      {|
      TStree := match find_subtree pathname (TStree (nthd n ts)) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0 (synced_dirfile f0))
                      (TStree (nthd n ts))
                | Some (TreeDir _ _) => TStree (nthd n ts)
                | None => TStree (nthd n ts)
                end;
      TSilist := TSilist (nthd n ts);
      TSfree := TSfree (nthd n ts) |}.
Proof.
(* skipped proof tokens: 556 *)
Admitted.
Lemma treeseq_sync_safe_sync: forall Fm fsxp Ftop mscs sm Ftree ts ds n pathname pathname' f inum al,
    (Fm ✶ rep fsxp Ftop (update_subtree pathname (TreeFile inum (synced_dirfile f)) (TStree ts !!))
           (TSilist ts !!) (fst (TSfree ts !!), snd (TSfree ts !!)) mscs sm)%pred
        (list2nmem (dssync_vecs ds al) !!) ->
    (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) -> 
    Datatypes.length al = Datatypes.length (DFData f) ->
    (length al = length (DFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
    treeseq_safe pathname (MSAlloc mscs) ts !! (nthd n ts) ->
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    tree_rep Fm Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_safe pathname' (MSAlloc mscs) 
      (treeseq_one_file_sync ts !! pathname)
      (treeseq_one_file_sync (nthd n ts) pathname).
Proof.
(* skipped proof tokens: 645 *)
Admitted.
Ltac distinct_inodes' :=
    repeat match goal with
      | [ H: treeseq_in_ds _ _ _ _ _ ?ts _ |- tree_inodes_distinct (TStree ?ts !!) ] => 
        eapply treeseq_in_ds_tree_pred_latest in H as Hpred;
        eapply rep_tree_inodes_distinct; eapply Hpred
    end.
Theorem treeseq_file_sync_ok : forall fsxp inum mscs,
    {< ds sm ts Fm Ftop Ftree pathname f,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts!!)) ]]
    POST:hm' RET:^(mscs')
      exists ds' al sm',
       let ts' := ts_file_sync pathname ts in
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
         [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
          [[ forall pathname',
             treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
             treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
         [[ ds' = dssync_vecs ds al]] *
         [[ length al = length (DFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i ]] *
         [[ MSAlloc mscs = MSAlloc mscs' ]] *
         [[ (Ftree * pathname |-> File inum (synced_dirfile f))%pred (dir2flatmem2 (TStree ts' !!)) ]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} AFS.file_sync fsxp inum mscs.
Proof.
(* skipped proof tokens: 420 *)
Admitted.
Lemma treeseq_latest: forall (ts : treeseq),
    (ts !!, []) !! = ts !!.
Proof.
(* skipped proof tokens: 20 *)
Admitted.
Theorem treeseq_tree_sync_ok : forall fsxp mscs,
    {< ds sm ts Fm Ftop,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]]
    POST:hm' RET:^(mscs')
      exists sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (ds!!, nil)) (MSLL mscs') sm' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ((ts !!), nil) (ds!!, nil)]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} AFS.tree_sync fsxp mscs.
Proof.
(* skipped proof tokens: 170 *)
Admitted.
Lemma treeseq_safe_rename: forall pathname' mscs cwd dstnum0 dstents 
    dstbase dstname srcnum0 srcents srcbase srcname dnum tree_elem ts
      frees'_1 frees'_2 ilist' subtree,
    tree_names_distinct (TStree ts!!) ->
    tree_inodes_distinct (TStree ts!!) ->
    find_subtree cwd (TStree ts !!) = Some (TreeDir dnum tree_elem) ->
    find_subtree srcbase (TreeDir dnum tree_elem) = Some (TreeDir srcnum0 srcents) ->
    find_dirlist srcname srcents = Some subtree ->
    find_subtree dstbase
            (tree_prune srcnum0 srcents srcbase srcname (TreeDir dnum tree_elem)) =
          Some (TreeDir dstnum0 dstents) ->
    (forall inum' def', inum' <> srcnum0 -> inum' <> dstnum0 ->
               In inum' (tree_inodes
           (update_subtree cwd
              (tree_graft dstnum0 dstents dstbase dstname subtree
                 (tree_prune srcnum0 srcents srcbase srcname
                    (TreeDir dnum tree_elem))) (TStree ts !!))) ->
               selN (TSilist ts !!) inum' def' = selN ilist' inum' def') ->
    (~pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname') ->
    (~pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname') ->
    dirtree_safe (TSilist ts !!)
            (BFILE.pick_balloc (fst (TSfree ts !!), snd (TSfree ts !!))
               (MSAlloc mscs)) (TStree ts !!) ilist'
            (BFILE.pick_balloc (frees'_1, frees'_2) (MSAlloc mscs))
            (update_subtree cwd
               (tree_graft dstnum0 dstents dstbase dstname subtree
                  (tree_prune srcnum0 srcents srcbase srcname
                     (TreeDir dnum tree_elem))) (TStree ts !!)) ->
    treeseq_safe pathname' (MSAlloc mscs)
      {|
      TStree := update_subtree cwd
                  (tree_graft dstnum0 dstents dstbase dstname subtree
                     (tree_prune srcnum0 srcents srcbase srcname
                        (TreeDir dnum tree_elem))) (TStree ts !!);
      TSilist := ilist';
      TSfree := (frees'_1, frees'_2) |} ts !!.
Proof.
(* skipped proof tokens: 932 *)
Admitted.
Theorem treeseq_rename_ok : forall fsxp dnum srcbase (srcname:string) dstbase dstname mscs,
    {< ds sm ts Fm Ftop Ftree cwd tree_elem srcnum dstnum srcfile dstfile,
    PRE:hm
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ find_subtree cwd (TStree ts !!) = Some (TreeDir dnum tree_elem) ]] *
      [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> File srcnum srcfile
                * (cwd ++ dstbase ++ [dstname]) |-> File dstnum dstfile)%pred (dir2flatmem2 (TStree ts !!)) ]]
    POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ isError ok ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] \/
       [[ ok = OK tt ]] * exists d ds' ts' ilist' frees' tree',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
       [[ forall pathname',
           ~ pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname' ->
           ~ pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname' ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
       [[ ds' = (pushd d ds) ]] *
       [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
       [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
       [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> Nothing
                 * (cwd ++ dstbase ++ [dstname]) |-> File srcnum srcfile)%pred (dir2flatmem2 (TStree ts' !!)) ]])
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists d ds' ts' ilist' frees' tree' mscs',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
       [[ forall pathname',
           ~ pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname' ->
           ~ pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname' ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
       [[ ds' = (pushd d ds) ]] *
       [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
       [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
       [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> Nothing
                 * (cwd ++ dstbase ++ [dstname]) |-> File srcnum srcfile)%pred (dir2flatmem2 (TStree ts' !!)) ]]
   >} AFS.rename fsxp dnum srcbase srcname dstbase dstname mscs.
Proof.
(* skipped proof tokens: 567 *)
Admitted.
Lemma treeseq_safe_delete: forall pathname' pathname name dnum tree_elem ts ilist' mscs 
    frees'_1 frees'_2 Ftree file finum,
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    (Ftree ✶ (pathname ++ [name]) |-> File finum file)%pred(dir2flatmem2 (TStree ts !!)) ->
    find_subtree pathname (TStree ts !!) = Some (TreeDir dnum tree_elem) ->
    (forall inum def',
        (inum = dnum -> False) ->
        In inum (tree_inodes (TStree ts !!)) ->
        In inum
          (tree_inodes
             (update_subtree pathname
                (TreeDir dnum (delete_from_list name tree_elem)) (TStree ts !!))) ->
        selN (TSilist ts !!) inum def' = selN ilist' inum def')  ->
     dirtree_safe (TSilist ts !!)
          (BFILE.pick_balloc (fst (TSfree ts !!), snd (TSfree ts !!))
             (MSAlloc mscs)) (TStree ts !!) ilist'
          (BFILE.pick_balloc (frees'_1, frees'_2) (MSAlloc mscs))
          (update_subtree pathname
             (TreeDir dnum (delete_from_list name tree_elem)) (TStree ts !!)) ->
     (~pathname_prefix (pathname ++ [name]) pathname') -> 
     treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
     treeseq_pred
        (treeseq_safe pathname' (MSAlloc mscs)
           (pushd
              {|
              TStree := update_subtree pathname
                          (TreeDir dnum (delete_from_list name tree_elem))
                          (TStree ts !!);
              TSilist := ilist';
              TSfree := (frees'_1, frees'_2) |} ts) !!)
        (pushd
           {|
           TStree := update_subtree pathname
                       (TreeDir dnum (delete_from_list name tree_elem))
                       (TStree ts !!);
           TSilist := ilist';
           TSfree := (frees'_1, frees'_2) |} ts).
Proof.
(* skipped proof tokens: 610 *)
Admitted.
Theorem treeseq_delete_ok : forall fsxp dnum name mscs,
    {< ds sm ts pathname Fm Ftop Ftree tree_elem finum file,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ find_subtree pathname (TStree ts !!) = Some (TreeDir dnum tree_elem) ]] *
      [[ (Ftree * ((pathname++[name])%list) |-> File finum file)%pred (dir2flatmem2 (TStree ts !!)) ]]
    POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ isError ok ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] \/
       [[ ok = OK tt ]] * exists d ds' ts' tree' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm hm' *
        [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
        [[ forall pathname',
           ~ pathname_prefix (pathname ++ [name]) pathname' ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
        [[ tree' = update_subtree pathname
                      (delete_from_dir name (TreeDir dnum tree_elem)) (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * (pathname ++ [name]) |-> Nothing)%pred (dir2flatmem2 (TStree ts' !!)) ]])
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d ds' ts' mscs' tree' ilist' frees',
        LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
        [[ MSAlloc mscs' = MSAlloc mscs ]] *
        [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
        [[ forall pathname',
           ~ pathname_prefix (pathname ++ [name]) pathname' ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
        [[ tree' = update_subtree pathname
                      (delete_from_dir name (TreeDir dnum tree_elem)) (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * (pathname ++ [name]) |-> Nothing)%pred (dir2flatmem2 (TStree ts' !!)) ]]

    >} AFS.delete fsxp dnum name mscs.
Proof.
(* skipped proof tokens: 353 *)
Admitted.
Hint Extern 1 ({{_}} Bind (AFS.file_get_attr _ _ _) _) => apply treeseq_file_getattr_ok : prog.
Hint Extern 1 ({{_}} Bind (AFS.lookup _ _ _ _) _) => apply treeseq_lookup_ok : prog.
Hint Extern 1 ({{_}} Bind (AFS.read_fblock _ _ _ _) _) => apply treeseq_read_fblock_ok : prog.
Hint Extern 1 ({{_}} Bind (AFS.file_set_attr _ _ _ _) _) => apply treeseq_file_set_attr_ok : prog.
Hint Extern 1 ({{_}} Bind (AFS.update_fblock_d _ _ _ _ _) _) => apply treeseq_update_fblock_d_ok : prog.
Hint Extern 1 ({{_}} Bind (AFS.file_sync _ _ _ ) _) => apply treeseq_file_sync_ok : prog.
Hint Extern 1 ({{_}} Bind (AFS.file_truncate _ _ _ _) _) => apply treeseq_file_grow_ok : prog.
Hint Extern 1 ({{_}} Bind (AFS.tree_sync _ _ ) _) => apply treeseq_tree_sync_ok : prog.
Hint Extern 1 ({{_}} Bind (AFS.rename _ _ _ _ _ _ _) _) => apply treeseq_rename_ok : prog.
Hint Extern 1 ({{_}} Bind (AFS.delete _ _ _ _) _) => apply treeseq_delete_ok : prog.
End TREESEQ.
