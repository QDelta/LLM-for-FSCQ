Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Lia.
Require Import Hashmap.
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
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import GroupLog.
Require Import SuperBlock.
Require Import DiskSet.
Require Import AsyncFS.
Require Import String.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreeNames.
Require Import DirTreeSafe.
Require Import TreeCrash.
Require Import TreeSeq.
Require Import DirSep.
Require Import DirSepCrash.
Require Import SyncedMem.
Import TREESEQ.
Import DTCrash.
Import ListNotations.
Set Implicit Arguments.
Module ATOMICCP.
Parameter the_dnum : addr.
Parameter cachesize : nat.
Axiom cachesize_ok : cachesize <> 0.
Hint Resolve cachesize_ok.
Definition temp_fn := ".temp"%string.
Definition Off0 := 0.
Definition copydata fsxp src_inum tinum mscs :=
    let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
    let^ (mscs, b) <- AFS.read_fblock fsxp src_inum Off0 mscs;
    let^ (mscs) <- AFS.update_fblock_d fsxp tinum Off0 b mscs;
    let^ (mscs) <- AFS.file_sync fsxp tinum mscs;   
    let^ (mscs, ok) <- AFS.file_set_attr fsxp tinum attr mscs;
    Ret ^(mscs, ok).
Definition copy2temp fsxp src_inum tinum mscs :=
    let^ (mscs, ok) <- AFS.file_truncate fsxp tinum 1 mscs;  
    match ok with
    | Err e =>
      Ret ^(mscs, false)
    | OK _ =>
      let^ (mscs, ok) <- copydata fsxp src_inum tinum mscs;
      match ok with
      | Err _ => Ret ^(mscs, false)
      | OK _ => Ret ^(mscs, true)
      end
    end.
Definition copy_and_rename fsxp src_inum tinum (dstbase:list string) (dstname:string) mscs :=
    let^ (mscs, ok) <- copy2temp fsxp src_inum tinum mscs;
    match ok with
      | false =>
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        
        Ret ^(mscs, false)
      | true =>
        let^ (mscs, r) <- AFS.rename fsxp the_dnum [] temp_fn dstbase dstname mscs;
        match r with
        | OK _ =>
          let^ (mscs) <- AFS.tree_sync fsxp mscs;
          Ret ^(mscs, true)
        | Err e =>
          let^ (mscs) <- AFS.tree_sync fsxp mscs;
          Ret ^(mscs, false)
        end
    end.
Definition atomic_cp fsxp src_inum dstbase dstname mscs :=
    let^ (mscs, r) <- AFS.create fsxp the_dnum temp_fn mscs;
    match r with
      | Err _ => Ret ^(mscs, false)
      | OK tinum =>
        let^ (mscs) <- AFS.tree_sync fsxp mscs;   
        let^ (mscs, ok) <- copy_and_rename fsxp src_inum tinum dstbase dstname mscs;
        Ret ^(mscs, ok)
    end.
Definition atomic_cp_recover :=
    recover_res <- AFS.recover cachesize;
    match recover_res with
    | Err e => Ret (Err e)
    | OK (mscs, fsxp) =>
      let^ (mscs, r) <- AFS.lookup fsxp the_dnum [temp_fn] mscs;
      match r with
      | Err _ => Ret (OK (mscs, fsxp))
      | OK (src_inum, isdir) =>
        let^ (mscs, ok) <- AFS.delete fsxp the_dnum temp_fn mscs;
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        match ok with
        | Err e => Ret (Err e)
        | OK _ => Ret (OK (mscs, fsxp))
        end
      end
    end.
Opaque LOG.idempred.
Opaque crash_xform.
Notation MSLL := BFILE.MSLL.
Notation MSAlloc := BFILE.MSAlloc.
Definition tree_with_src Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) dstbase dstname dstfile:  @pred _ (list_eq_dec string_dec) _ :=
   (exists dstinum,
    Ftree * nil |-> Dir the_dnum * 
            srcpath |-> File srcinum file *
            tmppath |-> Nothing *
            (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred.
Definition tree_with_tmp Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) tinum tfile dstbase dstname dstfile:  @pred _ (list_eq_dec string_dec) _ :=
   (exists dstinum,
    Ftree * nil |-> Dir the_dnum * 
            srcpath |-> File srcinum file *
            tmppath |-> File tinum tfile *
            (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred.
Definition tree_with_dst Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) dstbase dstname :  @pred _ (list_eq_dec string_dec) _ :=
   (exists dstinum,
    Ftree * nil |-> Dir the_dnum *
            srcpath |-> File srcinum file *
            tmppath |-> Nothing *
            (dstbase ++ [dstname])%list |-> File dstinum file)%pred.
Definition tree_rep Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) tinum dstbase dstname dstfile t := 
    (tree_names_distinct (TStree t)) /\
    (file = synced_dirfile file) /\
    ((exists tfile', 
      tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile (dir2flatmem2 (TStree t))) \/
     (tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile (dir2flatmem2 (TStree t))) \/
     (tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname (dir2flatmem2 (TStree t))))%type.
Definition tree_rep_recover Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) dstbase dstname dstfile t :=
    (tree_names_distinct (TStree t)) /\
    (file = synced_dirfile file) /\
    ((exists dstfile',
      tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile' *
      [[ file_crash dstfile dstfile' ]])%pred (dir2flatmem2 (TStree t)) \/
     (tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname)%pred (dir2flatmem2 (TStree t)))%type.
Lemma dirents2mem2_treeseq_one_upd_tmp : forall (F: @pred _ (@list_eq_dec string string_dec) _) tree tmppath inum f off v,
    let f' := {|
             DFData := (DFData f) ⟦ off := v ⟧;
             DFAttr := DFAttr f |} in
    tree_names_distinct (TStree tree) ->
    (F * tmppath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * tmppath |-> File inum f')%pred (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
Proof.
(* original proof tokens: 95 *)
unfold treeseq_one_upd.
(* No more tactics to try *)
Admitted.

Lemma treeseq_one_upd_tree_rep_tmp: forall tree Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstfile off v,
   let tfile' := {|
             DFData := (DFData tfile) ⟦ off := v ⟧;
             DFAttr := DFAttr tfile |} in
    tree_names_distinct (TStree tree) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile' dstbase dstname dstfile (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
Proof.
(* original proof tokens: 67 *)
unfold tree_with_tmp.
unfold tree_with_tmp; intros.
(* No more tactics to try *)
Admitted.

Lemma dirents2mem2_treeseq_one_upd_src : forall (F: @pred _ (@list_eq_dec string string_dec) _) F1 tree tmppath srcpath inum f off v,
    tree_names_distinct (TStree tree) ->
    (F1 * tmppath |-> Nothing)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
Proof.
(* original proof tokens: 95 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_one_upd_tree_rep_src: forall tree Ftree srcpath tmppath src_inum file dstbase dstname dstfile off v,
    tree_names_distinct (TStree tree) ->
    tree_with_src Ftree srcpath tmppath src_inum file dstbase dstname dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_src Ftree srcpath tmppath src_inum file dstbase dstname dstfile (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Lemma tsupd_d_in_exists: forall ts t tmppath off v,
    d_in t (tsupd ts tmppath off v) ->
    exists x, d_in x ts /\ t = (treeseq_one_upd x tmppath off v).
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_d_in: forall ts t Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    d_in t ts ->
    tree_names_distinct (TStree t).
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_treeseq_one_upd: forall ts t t' off vs Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    d_in t ts -> t' = treeseq_one_upd t tmppath off vs ->
    tree_names_distinct (TStree t').
Proof.
(* original proof tokens: 124 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_upd_tree_rep: forall ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile (v0:BFILE.datatype) t0,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) (tsupd ts tmppath Off0 (fst v0, vsmerge t0)).
Proof.
(* original proof tokens: 273 *)

(* No more tactics to try *)
Admitted.

Lemma dirents2mem2_treeseq_one_file_sync_tmp : forall (F: @pred _ (@list_eq_dec string string_dec) _) tree tmppath inum f,
    let f' := synced_dirfile f in
    tree_names_distinct (TStree tree) ->
    (F * tmppath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * tmppath |-> File inum f')%pred (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
Proof.
(* original proof tokens: 95 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_one_file_sync_tree_rep_tmp: forall tree Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstfile,
   let tfile' := synced_dirfile tfile in
    tree_names_distinct (TStree tree) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile' dstbase dstname dstfile (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
Proof.
(* original proof tokens: 67 *)

(* No more tactics to try *)
Admitted.

Lemma tssync_d_in_exists: forall ts t tmppath,
    d_in t (ts_file_sync tmppath ts) ->
    exists x, d_in x ts /\ t = (treeseq_one_file_sync x tmppath).
Proof.
(* original proof tokens: 70 *)

(* No more tactics to try *)
Admitted.

Lemma dirents2mem2_treeseq_one_file_sync_src : forall (F: @pred _ (@list_eq_dec string string_dec) _) F1 tree srcpath tmppath inum f,
    tree_names_distinct (TStree tree) ->
    (F1 * tmppath |-> Nothing)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
Proof.
(* original proof tokens: 95 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_one_file_sync_tree_rep_src: forall tree Ftree srcpath tmppath src_inum file  tfile dstbase dstname dstfile,
    let tfile' := BFILE.synced_file tfile in
    tree_names_distinct (TStree tree) ->
    tree_with_src Ftree srcpath tmppath src_inum file  dstbase dstname dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_src Ftree srcpath tmppath src_inum file  dstbase dstname dstfile (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_treeseq_one_file_sync: forall ts t t' Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
      treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
      d_in t ts -> t' = treeseq_one_file_sync t tmppath ->
      tree_names_distinct (TStree t').
Proof.
(* original proof tokens: 124 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_tssync_tree_rep: forall ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile)  (ts_file_sync tmppath ts).
Proof.
(* original proof tokens: 255 *)

(* No more tactics to try *)
Admitted.

Lemma length_synced_tmpfile : forall a v f,
    (a |-> v)%pred (list2nmem (DFData f)) ->
    Datatypes.length (synced_list (map fst (DFData f))) <= 1.
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Hint Resolve length_synced_tmpfile.
Lemma treerep_synced_dirfile: 
    forall Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile ts,
    treeseq_pred
      (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    file = synced_dirfile file.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Hint Resolve treerep_synced_dirfile.
Theorem copydata_ok : forall fsxp srcinum tmppath tinum mscs,
    {< ds sm ts Fm Ftop Ftree srcpath file tfile v0 t0 dstbase dstname dstfile,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[[ DFData tfile ::: (Off0 |-> t0) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts' sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
        (([[ isError r ]] *
          exists f', [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]])
         \/ ([[ r = OK tt ]] *
             [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  (synced_dirfile file) dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
      exists ds' sm' ts' mscs',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
      >} copydata fsxp srcinum tinum mscs.
Proof.
(* original proof tokens: 601 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (copydata _ _ _ _) _) => apply copydata_ok : prog.
Hint Extern 0 (okToUnify (tree_with_tmp _ _ _ _ _ _ _ _ _) (tree_with_tmp _ _ _ _ _ _ _ _ _)) => constructor : okToUnify.
Theorem copy2temp_ok : forall fsxp srcinum tinum mscs,
    {< Fm Ftop Ftree ds sm ts tmppath srcpath file tfile v0 dstbase dstname dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[ 1 >= Datatypes.length (DFData tfile) ]]
    POST:hm' RET:^(mscs', r)
      exists ds' sm' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
        (([[ r = false ]] *
          exists f',
          [[ (tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!))) ]])
         \/ ([[ r = true ]] *
             [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  (synced_dirfile file) dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
     exists ds' sm' ts' mscs',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
    >} copy2temp fsxp srcinum tinum mscs.
Proof.
(* original proof tokens: 273 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.
Lemma tree_with_tmp_the_dnum: forall Fm Ftop fsxp sm mscs Ftree srcpath tmppath srcinum file tinum
      tfile dstbase dstname dstfile ts ds,
    treeseq_in_ds Fm Ftop sm fsxp mscs ts ds ->
    tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile dstbase dstname dstfile
          (dir2flatmem2 (TStree ts !!)) ->
    exists direlem, 
        find_subtree [] (TStree ts !!) = Some (TreeDir the_dnum direlem).
Proof.
(* original proof tokens: 134 *)

(* No more tactics to try *)
Admitted.

Lemma tree_with_tmp_tmp_dst: forall Fm Ftop fsxp sm mscs Ftree srcpath tmppath srcinum file tinum
      tfile dstbase dstname dstfile ts ds,
    treeseq_in_ds Fm Ftop sm fsxp mscs ts ds ->
    tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile dstbase dstname dstfile
          (dir2flatmem2 (TStree ts !!)) ->
    (exists F' dstinum, ((F' ✶ ((tmppath)%list |-> File tinum tfile)
        ✶ (dstbase ++ [dstname])%list |-> File dstinum dstfile  )%pred (dir2flatmem2 (TStree ts !!))) /\
      (F' = (Ftree ✶ ([] |-> Dir the_dnum) ✶ srcpath |-> File srcinum file)%pred)).
Proof.
(* original proof tokens: 72 *)

(* No more tactics to try *)
Admitted.

Theorem copy_and_rename_ok : forall fsxp srcinum tinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree ds sm ts srcpath file tfile v0 dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[ dirtree_inum (TStree ts!!) = the_dnum ]] *
      [[ 1 >= Datatypes.length (DFData tfile) ]]
    POST:hm' RET:^(mscs', r)
      exists ds' sm' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]] *
       (([[r = false ]] *
        (exists f',
         [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]])) \/
       ([[r = true ]] *
          [[ tree_with_dst Ftree srcpath [temp_fn] srcinum file dstbase dstname (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
      exists ds' ts' sm' mscs',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]]
    >} copy_and_rename fsxp srcinum tinum dstbase dstname mscs.
Proof.
(* original proof tokens: 548 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (copy_and_rename _ _ _ _ _ _) _) => apply copy_and_rename_ok : prog.
Lemma rep_tree_crash: forall Fm fsxp Ftop d t ilist frees sm mscs d' msll',
    (Fm * rep fsxp Ftop t ilist frees mscs sm)%pred (list2nmem d) ->
    crash_xform (diskIs (list2nmem d)) (list2nmem d') ->
    (exists t', [[ tree_crash t t' ]] * (crash_xform Fm) *
      rep fsxp (BFileCrash.flist_crash_xform Ftop) t' ilist frees (BFILE.ms_empty msll') sm_synced
    )%pred (list2nmem d').
Proof.
(* original proof tokens: 76 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_tree_crash_exists: forall Fm Ftop fsxp sm mscs ts ds n d msll',
    let t := (nthd n ts) in
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    (exists t', [[ tree_crash (TStree t) t' ]] *
     (crash_xform Fm) * 
     rep fsxp (BFileCrash.flist_crash_xform Ftop) t' (TSilist t) (TSfree t) (BFILE.ms_empty msll') sm_synced
    )%pred (list2nmem d).
Proof.
(* original proof tokens: 140 *)
intros Fm Ftop fsxp sm mscs ts ds n d msll' t H H0.
exists (TStree t).
revert H H0.
(* No more tactics to try *)
Admitted.

Lemma treeseq_in_ds_crash: forall Fm Ftop fsxp d (t: dirtree) n ts sm ms,
    BFILE.MSinitial ms ->
    (crash_xform Fm
      ✶ rep fsxp Ftop t (TSilist (nthd n ts))
          (TSfree (nthd n ts)) (BFILE.ms_empty (MSLL ms)) sm)%pred (list2nmem d) ->
    treeseq_in_ds (crash_xform Fm) Ftop fsxp sm ms
        ({| TStree := t; TSilist := TSilist (nthd n ts); TSfree := TSfree (nthd n ts) |}, []) 
        (d, []).
Proof.
(* original proof tokens: 143 *)

(* No more tactics to try *)
Admitted.

Lemma find_name_dirtree_inum: forall t inum,
    find_name [] t = Some (inum, true) ->
    dirtree_inum t = inum.
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Lemma find_name_dirtree_isdir: forall t inum,
    find_name [] t = Some (inum, true) ->
    dirtree_isdir t = true.
Proof.
(* original proof tokens: 43 *)
(* generated proof tokens: 68 *)

intros t inum H.
 destruct t.
 - simpl in H. discriminate H.
 - simpl in H. destruct H as [H1 H2]. (* Extract the results from the find_name *)
   (* Since we have matched with TreeDir, we know it is indeed a directory *)
   auto.
Qed.

Lemma tree_rep_find_subtree_root: forall Frest Ftree t,
    tree_names_distinct t ->
    (Frest * (Ftree ✶ [] |-> Dir the_dnum))%pred (dir2flatmem2 t) ->
    (exists elem, find_subtree [] t = Some (TreeDir the_dnum elem)).
Proof.
(* original proof tokens: 59 *)

(* No more tactics to try *)
Admitted.

Lemma tree_rep_find_name_root: forall Frest Ftree t,
    tree_names_distinct t ->
    (Frest * (Ftree ✶ [] |-> Dir the_dnum))%pred (dir2flatmem2 t) ->
    find_name [] t = Some (the_dnum , true).
Proof.
(* original proof tokens: 59 *)

(* No more tactics to try *)
Admitted.

Lemma tree_pred_crash_find_subtree_root: forall Ftree srcpath tmppath srcinum file tinum dstbase 
      dstname dstfile ts n t',
    let t := (nthd n ts) in
    treeseq_pred
     (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    tree_crash (TStree t) t' ->
    (exists elem, find_subtree [] t' = Some (TreeDir the_dnum elem)).
Proof.
(* original proof tokens: 277 *)
intros Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile ts n t' Hpred Hcrash.
(* No more tactics to try *)
Admitted.

Lemma tree_pred_crash_find_name_root: forall Ftree srcpath tmppath srcinum file tinum dstbase 
      dstname dstfile ts n t',
    let t := (nthd n ts) in
    treeseq_pred
     (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    tree_crash (TStree t) t' ->
    find_name [] t' = Some (the_dnum, true).
Proof.
(* original proof tokens: 69 *)
intros Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile ts n t' Hpred Hcrash.
(* No more tactics to try *)
Admitted.

Lemma treeseq_pred_d_in : forall p ts t,
    treeseq_pred p ts ->
    d_in t ts ->
    p t.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_pred_nthd : forall p ts n,
    treeseq_pred p ts ->
    p (nthd n ts).
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_pred_tree_rep_dir2flatmem2 : forall ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    treeseq_pred (fun t =>
      ((exists tfile', 
        tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile) \/
       (tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile) \/
       (tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname))%pred
      (dir2flatmem2 (TStree t))) ts.
Proof.
(* original proof tokens: 63 *)

(* No more tactics to try *)
Admitted.

Lemma tree_with_tmp_find_name : forall Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile v t,
    flatmem_crash_xform
        ((exists tfile' : dirfile,
            tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile)
        \/ tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile
        \/ tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname)%pred
        (dir2flatmem2 t) ->
    Some v = find_name tmppath t ->
    tree_names_distinct t ->
    flatmem_crash_xform
        ((exists tfile' : dirfile,
            tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile))%pred
        (dir2flatmem2 t).
Proof.
(* original proof tokens: 265 *)

(* No more tactics to try *)
Admitted.

Lemma tree_with_tmp_find_name_none : forall Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t,
    flatmem_crash_xform
        ((exists tfile' : dirfile,
            tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile)
        \/ tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile
        \/ tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname)%pred
        (dir2flatmem2 t) ->
    None = find_name tmppath t ->
    tree_names_distinct t ->
    flatmem_crash_xform
        (tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile \/
         tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname)%pred
        (dir2flatmem2 t).
Proof.
(* original proof tokens: 179 *)

(* No more tactics to try *)
Admitted.

Lemma in_add_to_list_or: forall  tree name name' f,
  In name' (map fst (add_to_list name f tree)) ->
  name = name' \/ In name' (map fst tree).
Proof.
(* original proof tokens: 87 *)

(* No more tactics to try *)
Admitted.

Lemma in_add_to_list_tree_or: forall  tree name t t',
  In t (add_to_list name t' tree) ->
  t = (name, t') \/ In t tree.
Proof.
(* original proof tokens: 101 *)

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

Lemma NoDup_add_to_list: forall tree f fname,
  NoDup (map fst tree) ->
  ~ In fname (map fst tree) ->
  NoDup (map fst (add_to_list fname f tree)).
Proof.
(* original proof tokens: 154 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_tree_rep_sync_after_create: forall x0 (F: pred) dummy1 dummy5 srcinum dummy6 dummy4 dstbase
           dstname dummy9 temp_fn x a6 dummy3 a4 a5_1 a5_2,
  treeseq_pred
        (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
           dstname dummy9) dummy3 ->
  TStree dummy3 !! = TreeDir the_dnum x ->
  (F ✶ [temp_fn]%list |-> Nothing)%pred (dir2flatmem2 (TStree dummy3 !!)) ->
  (((((dstbase ++ [dstname])%list |-> File x0 dummy9
          ✶ dummy5 |-> File srcinum dummy6) ✶ [] |-> Dir the_dnum) ✶ dummy1)
       ✶ [temp_fn]%list |-> File a6 dirfile0)%pred
        (dir2flatmem2
           (tree_graft the_dnum x [] temp_fn (TreeFile a6 dirfile0)
              (TStree dummy3 !!))) ->
  treeseq_pred
  (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 a6 dstbase dstname
     dummy9)
  ({|
   TStree := tree_graft the_dnum x [] temp_fn (TreeFile a6 dirfile0)
               (TStree dummy3 !!);
   TSilist := a4;
   TSfree := (a5_1, a5_2) |}, []).
Proof.
(* original proof tokens: 309 *)

(* No more tactics to try *)
Admitted.

Ltac synced_file_eq :=
    try match goal with
    | [ H : file_crash ?f ?f |- _ ] => clear H
    end;
    match goal with
    | [ H1 : treeseq_pred (tree_rep _ _ _ _ ?file _ _ _ _) _,
        H2 : file_crash ?file ?file' |- _ ] =>
      let Hx := fresh in
      let Hy := fresh in
      eapply treerep_synced_dirfile in H1 as Hx;
      erewrite Hx in H2;
      eapply file_crash_synced in H2 as Hy;
      try rewrite Hy in *;
      try rewrite <- Hx in *;
      clear Hx; clear Hy
    end.
Theorem atomic_cp_ok : forall fsxp srcinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree ds sm ts srcpath file v0 dstfile tinum,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_src Ftree srcpath [temp_fn] srcinum file dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[ dirtree_inum (TStree ts!!) = the_dnum ]]
    POST:hm' RET:^(mscs', r)
      exists ds' sm' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       (([[r = false ]] *
        ([[ treeseq_in_ds Fm Ftop fsxp sm' mscs ts' ds' ]] *
          [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file 
                    tinum dstbase dstname dstfile) ts' ]] *
          [[ tree_with_src Ftree srcpath [temp_fn] srcinum file 
                    dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] 
                \/
         (exists f' tinum',
         [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
         [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file
                     tinum' dstbase dstname dstfile) ts' ]] *
         [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum' 
                    f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]))) 
        \/
       (exists tinum',
          [[r = true ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
          [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file 
                          tinum' dstbase dstname dstfile) ts' ]] *
          [[ tree_with_dst Ftree srcpath [temp_fn] srcinum file 
                    dstbase dstname (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
      exists mscs' ds' ts' sm',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       ((exists tinum, [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts']])
       \/ (exists t dfile tinum', [[ ts' = pushd t ts ]] * 
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum' dstbase dstname dfile t ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]]))
    >} atomic_cp fsxp srcinum dstbase dstname mscs.
Proof.
(* original proof tokens: 1491 *)

(* No more tactics to try *)
Admitted.

Theorem atomic_cp_recover_ok_1 :
    {< Fm Ftop Ftree fsxp cs mscs ds sm ts srcpath file srcinum tinum dstfile (dstbase: list string) (dstname:string),
    PRE:hm
      LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts]]
    POST:hm' RET:r
      [[ isError r ]] * any \/
      exists d sm' t mscs',
      [[ r = OK (mscs', fsxp) ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') sm' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' (t, nil) (d, nil) ]] *
      [[ treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dstfile) (t, nil) ]]
    XCRASH:hm'
      (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]])
       \/
      exists ts' ds' sm' mscs' dstfile',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' ts' ds' ]] *
      [[ treeseq_pred (tree_rep (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile') ts' ]] *
      [[ file_crash dstfile dstfile' ]]
    >} atomic_cp_recover.
Proof.
(* original proof tokens: 2799 *)
remember (atomic_cp_recover) as x.
intros; unfold atomic_cp_recover in *; simpl in *.
intros; subst x.
(* No more tactics to try *)
Admitted.

Lemma tree_pred_crash_find_name_root_single: forall Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t t',
    tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t ->
    tree_crash (TStree t) t' ->
    find_name [] t' = Some (the_dnum, true).
Proof.
(* original proof tokens: 149 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_in_ds_snd_length: forall Fm Ftop fsxp sm mscs t tl d dl, 
  treeseq_in_ds Fm Ftop fsxp sm mscs (t, tl) (d, dl) ->
  List.length tl = List.length dl.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma tree_pred_crash_find_subtree_root_single: forall Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t t',
    tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t ->
    tree_crash (TStree t) t' ->
    (exists elem, find_subtree [] t' = Some (TreeDir the_dnum elem)).
Proof.
(* original proof tokens: 157 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_in_ds_crash_single: forall Fm Ftop fsxp d x t sm ms,
  BFILE.MSinitial ms ->
  (crash_xform Fm
    ✶ rep fsxp Ftop x (TSilist t)
        (TSfree t) (BFILE.ms_empty (MSLL ms)) sm)%pred (list2nmem d) ->
  treeseq_in_ds (crash_xform Fm) Ftop fsxp sm ms
      ({| TStree := x; TSilist := TSilist t; TSfree := TSfree t |}, []) 
      (d, []).
Proof.
(* original proof tokens: 141 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_pred_tree_rep_dir2flatmem2_single : forall t Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
  tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t ->
    ((exists tfile', 
      tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile) \/
     (tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile) \/
     (tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname))%pred
    (dir2flatmem2 (TStree t)).
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma add_to_list_not_in: forall d s t,
  ~In s (map fst d) -> add_to_list s t d = (d ++ [(s,t)])%list.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_add_to_dir: forall ents tfn a df inum,
  ~In tfn (map fst ents) -> 
  tree_names_distinct (TreeDir inum ents) ->
  tree_names_distinct (add_to_dir tfn (TreeFile a df) (TreeDir inum ents)).
Proof.
(* original proof tokens: 296 *)

(* No more tactics to try *)
Admitted.

Theorem atomic_cp_recover_ok_2 :
    {< Fm Ftop Ftree fsxp cs mscs ds sm srcpath file srcinum tinum tinum' dfile dstfile (dstbase: list string) (dstname:string) t ts',
    PRE:hm
      LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs (pushd t ts') ds ]] *
      [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum' dstbase dstname dfile t ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]]
    POST:hm' RET:r
      [[ isError r ]] * any \/
      exists d sm' t mscs',
      [[ r = OK (mscs', fsxp) ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') sm' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' (t, nil) (d, nil) ]] *
      ([[ treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dstfile) (t, nil) ]] \/
       [[ treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dfile) (t, nil) ]])
    XCRASH:hm'
      (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs (pushd t ts') ds ]] *
      [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum' dstbase dstname dfile t ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]])
       \/
      exists ts' ds' sm' mscs' dstfile' tinum',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' ts' ds' ]] *
      [[ treeseq_pred (tree_rep (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file tinum' dstbase dstname dstfile') ts' ]] *
      ([[ file_crash dstfile dstfile' ]] \/ [[ file_crash dfile dstfile' ]])
    >} atomic_cp_recover.
Proof.
(* original proof tokens: 5774 *)

(* No more tactics to try *)
Admitted.

End ATOMICCP.
