Require Import Coq.Strings.String.
Require Import Prog ProgMonad.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Lia.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirCache.
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
Require Import SyncedMem.
Require Import GroupLog.
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeInodes.
Require Import DirTreeSafe.
Set Implicit Arguments.
Import DirTree.
Import ListNotations.
Module AFS.
Definition compute_xparams (data_bitmaps inode_bitmaps log_descr_blocks : addr) :=
    

    

    
    let data_blocks := data_bitmaps * valulen in
    let inode_blocks := inode_bitmaps * valulen / INODE.IRecSig.items_per_val in
    let inode_base := data_blocks in
    let balloc_base1 := inode_base + inode_blocks + inode_bitmaps in
    let balloc_base2 := balloc_base1 + data_bitmaps in
    let log_hdr := 1 + balloc_base2 + data_bitmaps in
    let log_descr := log_hdr + 1 in
    let log_data := log_descr + log_descr_blocks in
    let log_data_size := log_descr_blocks * PaddedLog.DescSig.items_per_val in
    let max_addr := log_data + log_data_size in
    (Build_fs_xparams
     (Build_log_xparams 1 log_hdr log_descr log_descr_blocks log_data log_data_size)
     (Build_inode_xparams inode_base inode_blocks)
     (Build_balloc_xparams balloc_base1 data_bitmaps)
     (Build_balloc_xparams balloc_base2 data_bitmaps)
     (Build_balloc_xparams (inode_base + inode_blocks) inode_bitmaps)
     1
     max_addr).
Lemma compute_xparams_ok : forall data_bitmaps inode_bitmaps log_descr_blocks magic,
    goodSize addrlen magic ->
    goodSize addrlen (1 +
          data_bitmaps * valulen +
          inode_bitmaps * valulen / INODE.IRecSig.items_per_val +
          inode_bitmaps + data_bitmaps + data_bitmaps +
          1 + log_descr_blocks + log_descr_blocks * PaddedLog.DescSig.items_per_val) ->
    fs_xparams_ok (compute_xparams data_bitmaps inode_bitmaps log_descr_blocks magic).
Proof.
(* skipped proof tokens: 62 *)
Admitted.
Notation MSLL := BFILE.MSLL.
Notation MSAllocC := BFILE.MSAllocC.
Notation MSIAllocC := BFILE.MSIAllocC.
Notation MSICache := BFILE.MSICache.
Notation MSAlloc := BFILE.MSAlloc.
Notation MSDBlocks := BFILE.MSDBlocks.
Import DIRTREE.
Definition mkfs cachesize data_bitmaps inode_bitmaps log_descr_blocks :=
    let fsxp := compute_xparams data_bitmaps inode_bitmaps log_descr_blocks SB.magic_number in
    cs <- BUFCACHE.init_load cachesize;
    cs <- SB.init fsxp cs;
    mscs <- LOG.init (FSXPLog fsxp) cs;
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    ms <- BFILE.init (FSXPLog fsxp) (FSXPBlockAlloc1 fsxp, FSXPBlockAlloc2 fsxp) fsxp (FSXPInode fsxp) mscs;
    let^ (ialloc_ms, r) <- IAlloc.alloc (FSXPLog fsxp) fsxp (BFILE.MSIAlloc ms);
    let mscs := IAlloc.MSLog ialloc_ms in
    match r with
    | None =>
      mscs <- LOG.abort (FSXPLog fsxp) mscs;
      Ret (Err ENOSPCINODE)
    | Some inum =>
      
      If (eq_nat_dec inum (FSXPRootInum fsxp)) {
        let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
        If (bool_dec ok true) {
          mscs <- LOG.flushsync (FSXPLog fsxp) mscs;
          Ret (OK ((BFILE.mk_memstate (MSAlloc ms) mscs (MSAllocC ms) (IAlloc.MSCache ialloc_ms) (MSICache ms) (MSCache ms) (MSDBlocks ms)), fsxp))
        } else {
          Ret (Err ELOGOVERFLOW)
        }
      } else {
        mscs <- LOG.abort (FSXPLog fsxp) mscs;
        Ret (Err ELOGOVERFLOW)
      }
    end.
Lemma S_minus_1_helper : forall n a b,
    S (n + 1 + a + b) - 1 - n = S (a + b).
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma S_minus_1_helper2 : forall n,
    S n - 1 = n.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Ltac equate_log_rep :=
    match goal with
    | [ r : BFILE.memstate,
        H : context [ compute_xparams ?a1 ?a2 ?a3 ?a4 ],
        Hi: context [IAlloc.Alloc.rep _ _ _ _ ?x_]
        |- LOG.rep ?xp ?F ?d ?ms _ _ =p=> LOG.rep ?xp' ?F' ?d' ?ms' _ _ * _ ] =>
        equate d d'; equate ms' (MSLL (
        BFILE.mk_memstate (MSAlloc r) ms (MSAllocC r) (IAlloc.MSCache x_) (MSICache r) (MSCache r) (MSDBlocks r)
        ));
        equate xp' (FSXPLog (compute_xparams a1 a2 a3 a4))
    | [ r : BFILE.memstate,
        H : context [ compute_xparams ?a1 ?a2 ?a3 ?a4 ]
        |- LOG.rep ?xp ?F ?d ?ms _ _ =p=> LOG.rep ?xp' ?F' ?d' ?ms' _ _ * _ ] =>
        equate d d'; equate ms' (MSLL (
        BFILE.mk_memstate (MSAlloc r) ms (MSAllocC r) (IAlloc.Alloc.freelist0) (MSICache r) (MSCache r) (MSDBlocks r)
        ));
        equate xp' (FSXPLog (compute_xparams a1 a2 a3 a4))
    end.
Theorem mkfs_ok : forall cachesize data_bitmaps inode_bitmaps log_descr_blocks,
    {!!< disk,
     PRE:vm,hm
       arrayS 0 disk *
       [[ cachesize <> 0 /\ data_bitmaps <> 0 /\ inode_bitmaps <> 0 ]] *
       [[ data_bitmaps <= valulen * valulen /\ inode_bitmaps <= valulen * valulen ]] *
       [[ length disk = 1 +
          data_bitmaps * valulen +
          inode_bitmaps * valulen / INODE.IRecSig.items_per_val +
          inode_bitmaps + data_bitmaps + data_bitmaps +
          1 + log_descr_blocks + log_descr_blocks * PaddedLog.DescSig.items_per_val ]] *
       [[ goodSize addrlen (length disk) ]]
     POST:vm',hm' RET:r exists ms fsxp d sm,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL ms) sm hm' *
       [[ vm' = vm ]] *
       ( [[ isError r ]] \/ exists ilist frees,
         [[ r = OK (ms, fsxp) ]] *
         [[[ d ::: rep fsxp emp (TreeDir (FSXPRootInum fsxp) nil) ilist frees ms sm ]]] )
     CRASH:hm'
       any
     >!!} mkfs cachesize data_bitmaps inode_bitmaps log_descr_blocks.
Proof.
(* skipped proof tokens: 771 *)
Admitted.
Definition recover cachesize :=
    cs <- BUFCACHE.init_recover cachesize;
    let^ (cs, fsxp) <- SB.load cs;
    If (addr_eq_dec (FSXPMagic fsxp) SB.magic_number) {
      mscs <- LOG.recover (FSXPLog fsxp) cs;
      mscs <- BFILE.recover mscs;
      Ret (OK (mscs, fsxp))
    } else {
      Ret (Err EINVAL)
    }.
Definition file_get_attr fsxp inum ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, attr) <- DIRTREE.getattr fsxp inum (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), attr);
    t2 <- Rdtsc ;
    Debug "get_attr" (t2-t1) ;;
    Ret r.
Definition file_get_sz fsxp inum ams :=
    t1 <- Rdtsc ;
    let^ (ams, attr) <- file_get_attr fsxp inum ams;
    t2 <- Rdtsc ;
    Debug "file_get_sz" (t2-t1) ;;
    Ret ^(ams, INODE.ABytes attr).
Definition file_set_attr fsxp inum attr ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams' <- DIRTREE.setattr fsxp inum attr (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    let^ (ms', ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
    If (bool_dec ok true) {
      Ret ^((BFILE.mk_memstate (MSAlloc ams') ms' (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
    } else {
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms' (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
    }.
Definition file_set_sz fsxp inum sz ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.updattr fsxp inum (INODE.UBytes sz) (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
    If (bool_dec ok true) {
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK tt)
    } else {
      Ret ^(ams, Err ELOGOVERFLOW)
    }.
Definition read_fblock fsxp inum off ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, b) <- DIRTREE.read fsxp inum off (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), b);
    t2 <- Rdtsc ;
    Debug "read_fblock" (t2-t1) ;;
    Ret r.
Definition file_truncate fsxp inum sz ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams', ok) <- DIRTREE.truncate fsxp inum sz (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    r <- match ok with
    | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
    | OK _ =>
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
      If (bool_dec ok true) {
        Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
      } else {
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
      }
    end;
    t2 <- Rdtsc ;
    Debug "truncate" (t2-t1) ;;
    Ret r.
Definition ftruncate fsxp inum sz ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let sz_blocks := (sz + valulen - 1) / valulen in
    let^ (ams', ok) <- DIRTREE.truncate fsxp inum sz_blocks (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    r <- match ok with
    | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
    | OK _ =>
      ams' <- DIRTREE.updattr fsxp inum (INODE.UBytes (addr2w sz)) (BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams'));
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
      If (bool_dec ok true) {
        Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
      } else {
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)),
              Err ELOGOVERFLOW)
      }
    end;
    t2 <- Rdtsc ;
    Debug "ftruncate" (t2-t1) ;;
    Ret r.
Definition update_fblock_d fsxp inum off v ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.dwrite fsxp inum off v (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)));
    t2 <- Rdtsc ;
    Debug "update_fblock_d" (t2-t1) ;;
    Ret r.
Definition update_fblock fsxp inum off v ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.write fsxp inum off v (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), ok);
    t2 <- Rdtsc ;
    Debug "update_fblock" (t2-t1) ;;
    Ret r.
Definition file_sync fsxp inum ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.datasync fsxp inum (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)));
    t2 <- Rdtsc ;
    Debug "file_sync" (t2-t1) ;;
    Ret r.
Definition readdir fsxp dnum ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, files) <- SDIR.readdir (FSXPLog fsxp) (FSXPInode fsxp) dnum (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), files).
Definition create fsxp dnum name ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams', oi) <- DIRTREE.mkfile fsxp dnum name (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    r <- match oi with
      | Err e =>
          ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');
          Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
      | OK inum =>
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
        match ok with
          | true => Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK inum)
          | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
        end
     end;
     t2 <- Rdtsc ;
     Debug "create" (t2-t1) ;;
     Ret r.
Definition mksock fsxp dnum name ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, oi) <- DIRTREE.mkfile fsxp dnum name (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    match oi with
      | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
      | OK inum =>
        ams <- BFILE.updattr (FSXPLog fsxp) (FSXPInode fsxp) inum (INODE.UType $1) ams;
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
        match ok with
          | true => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK inum)
          | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
        end
    end.
Definition mkdir fsxp dnum name ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, oi) <- DIRTREE.mkdir fsxp dnum name (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    match oi with
      | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);
          Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
      | OK inum =>
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
        match ok with
          | true => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK inum)
          | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
        end
    end.
Definition delete fsxp dnum name ams :=
    t1 <- Rdtsc;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams', ok) <- DIRTREE.delete fsxp dnum name (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    res <- match ok with
    | OK _ =>
       let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
       match ok with
       | true => Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
       | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
       end
    | Err e =>
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
    end;
    t2 <- Rdtsc;
    Debug "delete" (t2-t1);;
    Ret res.
Definition lookup fsxp dnum names ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, r) <- DIRTREE.namei fsxp dnum names (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), r);
    t2 <- Rdtsc ;
    Debug "lookup" (t2-t1) ;;
    Ret r.
Definition rename fsxp dnum srcpath srcname dstpath dstname ams :=
    t1 <- Rdtsc;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams', r) <- DIRTREE.rename fsxp dnum srcpath srcname dstpath dstname (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    res <- match r with
    | OK _ =>
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
      match ok with
      | true => Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
      | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
      end
    | Err e =>
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
    end;
    t2 <- Rdtsc;
    Debug "rename" (t2-t1);;
    Ret res.
Definition tree_sync fsxp ams :=
    t1 <- Rdtsc ;
    ams <- DIRTREE.sync fsxp ams;
    t2 <- Rdtsc ;
    Debug "tree_sync" (t2-t1) ;;
    Ret ^(ams).
Definition tree_sync_noop fsxp ams :=
    ams <- DIRTREE.sync_noop fsxp ams;
    Ret ^(ams).
Definition umount fsxp ams :=
    ams <- DIRTREE.sync fsxp ams;
    ms <- LOG.sync_cache (FSXPLog fsxp) (MSLL ams);
    Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams))).
Definition statfs fsxp ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    
    ms <- LOG.commit_ro (FSXPLog fsxp) ms;
    
    Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), 0, 0).
Hint Extern 0 (okToUnify (LOG.rep_inner _ _ _ _) (LOG.rep_inner _ _ _ _)) => constructor : okToUnify.
Theorem recover_ok : forall cachesize,
    {< fsxp cs ds,
     PRE:hm
       LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
       [[ cachesize <> 0 ]]
     POST:hm' RET:r exists ms fsxp',
       [[ fsxp' = fsxp ]] * [[ r = OK (ms, fsxp') ]] *
       exists d n sm, [[ n <= length (snd ds) ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL ms) sm hm' *
       [[ sm = sm_synced ]] *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]] *
       [[ BFILE.MSinitial ms ]]
     XCRASH:hm'
       LOG.before_crash (FSXPLog fsxp) (SB.rep fsxp) ds hm'
     >} recover cachesize.
Proof.
(* skipped proof tokens: 623 *)
Admitted.
Hint Extern 1 ({{_}} Bind (recover _) _) => apply recover_ok : prog.
Ltac recover_ro_ok := intros;
    repeat match goal with
      | [ |- forall_helper _ ] => unfold forall_helper; intros; eexists; intros
      | [ |- corr3 ?pre' _ _ ] => eapply corr3_from_corr2_rx; eauto with prog
      | [ |- corr3 _ _ _ ] => eapply pimpl_ok3; intros
      | [ |- corr2 _ _ ] => step
      | [ H: crash_xform ?x =p=> ?x |- context [ crash_xform ?x ] ] => rewrite H
      | [ H: diskIs _ _ |- _ ] => unfold diskIs in *
      | [ |- pimpl (crash_xform _) _ ] => progress autorewrite with crash_xform
    end.
Hint Extern 0 (okToUnify (LOG.idempred _ _ _ _) (LOG.idempred _ _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (LOG.after_crash _ _ _ _ _) (LOG.after_crash _ _ _ _ _)) => constructor : okToUnify.
Theorem file_getattr_ok : forall fsxp inum mscs,
  {< ds sm pathname Fm Ftop tree f ilist frees,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
         [[ r = DFAttr f /\ MSAlloc mscs' = MSAlloc mscs /\ MSCache mscs' = MSCache mscs ]]
  CRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} file_get_attr fsxp inum mscs.
Proof.
(* skipped proof tokens: 154 *)
Admitted.
Hint Extern 1 ({{_}} Bind (file_get_attr _ _ _) _) => apply file_getattr_ok : prog.
Theorem file_get_sz_ok : forall fsxp inum mscs,
  {< ds sm pathname Fm Ftop tree f ilist frees,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
         [[ r = INODE.ABytes (DFAttr f) /\ MSAlloc mscs' = MSAlloc mscs ]]
  CRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} file_get_sz fsxp inum mscs.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Hint Extern 1 ({{_}} Bind (file_get_sz _ _ _) _) => apply file_get_sz_ok : prog.
Ltac xcrash_solve :=
    repeat match goal with
      | [ H: forall _ _ _,  _ =p=> (?crash _) |- _ =p=> (?crash _) ] => eapply pimpl_trans; try apply H; cancel
      | [ |- crash_xform (LOG.rep _ _ _ _ _ _) =p=> _ ] => rewrite LOG.notxn_intact; cancel
      | [ H: crash_xform ?rc =p=> _ |- crash_xform ?rc =p=> _ ] => rewrite H; xform_norm
    end.
Ltac intuition' :=
    match goal with
    | [|- _ /\ _]  => split; intuition'
    | [|- True] => auto
    | _ => idtac
  end.
Ltac simpl_idempred_l :=
    simpl;
    repeat xform_dist;
    repeat xform_deex_l;
    xform_dist;
    rewrite crash_xform_lift_empty;
    norml; unfold stars; simpl;
    match goal with
    | [ H: crash_xform ?x =p=> crash_xform _ |- context[crash_xform ?x] ] => rewrite H
    end;
    repeat xform_dist;
    try rewrite sep_star_or_distr;
    rewrite LOG.crash_xform_idempred.
Ltac simpl_idempred_r :=
      recover_ro_ok;
      (norml; unfold stars; simpl);
      (norm'r; unfold stars; simpl);
      try (cancel);
      intuition';
      repeat xform_dist;
      repeat rewrite crash_xform_idem.
Theorem read_fblock_ok : forall fsxp inum off mscs,
    {< ds sm Fm Ftop tree pathname f Fd vs ilist frees,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs', r)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
           [[ r = fst vs /\ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_fblock fsxp inum off mscs.
Proof.
(* skipped proof tokens: 138 *)
Admitted.
Hint Extern 1 ({{_}} Bind (read_fblock _ _ _ _) _) => apply read_fblock_ok : prog.
Theorem file_set_attr_ok : forall fsxp inum attr mscs,
  {< ds sm pathname Fm Ftop tree f ilist frees,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ isError ok  ]] *
       (LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
        [[ BFILE.mscs_same_except_log mscs mscs' ]] *
        [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]]) \/
      ([[ ok = OK tt  ]] * exists d tree' f' ilist',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm' *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees mscs' sm)]]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
        [[ f' = mk_dirfile (DFData f) attr ]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
        [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]])
     )
  XCRASH:hm'
    LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
    exists d tree' f' ilist' mscs',
    [[ MSAlloc mscs' = MSAlloc mscs ]] *
    LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
    [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees mscs' sm)]]] *
    [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
    [[ f' = mk_dirfile (DFData f) attr ]] *
    [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                    ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
    [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]]
  >} file_set_attr fsxp inum attr mscs.
Proof.
(* skipped proof tokens: 186 *)
Admitted.
Hint Extern 1 ({{_}} Bind (file_set_attr _ _ _ _) _) => apply file_set_attr_ok : prog.
Theorem file_truncate_ok : forall fsxp inum sz mscs,
    {< ds sm Fm Ftop tree pathname f ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs', r)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
         ([[ isError r ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] \/
      [[ r = OK tt ]] * exists d tree' f' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm' *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)]]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
        [[ f' = mk_dirfile (setlen (DFData f) sz ($0, nil)) (DFAttr f) ]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
        [[ sz >= Datatypes.length (DFData f) -> BFILE.treeseq_ilist_safe inum ilist ilist' ]] )
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d tree' f' ilist' frees' mscs',
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
      [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)]]] *
      [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
      [[ f' = mk_dirfile (setlen (DFData f) sz ($0, nil)) (DFAttr f) ]] *
      [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
      [[ sz >= Datatypes.length (DFData f) -> BFILE.treeseq_ilist_safe inum ilist ilist' ]]
    >} file_truncate fsxp inum sz mscs.
Proof.
(* skipped proof tokens: 172 *)
Admitted.
Hint Extern 1 ({{_}} Bind (file_truncate _ _ _ _) _) => apply file_truncate_ok : prog.
Ltac latest_rewrite := unfold latest, pushd; simpl.
Theorem update_fblock_d_ok : forall fsxp inum off v mscs,
    {< ds sm Fm Ftop tree pathname f Fd vs frees ilist,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs')
      exists tree' f' ds' sm' bn,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
       [[ BFILE.block_belong_to_file ilist bn inum off ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
       
       [[[ ds'!! ::: (Fm  * rep fsxp Ftop tree' ilist frees mscs' sm') ]]] *
       [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
       [[[ (DFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
       [[ DFAttr f' = DFAttr f ]] *
       [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                       ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists bn, [[ BFILE.block_belong_to_file ilist bn inum off ]] *
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (dsupd ds bn (v, vsmerge vs)) hm'
   >} update_fblock_d fsxp inum off v mscs.
Proof.
(* skipped proof tokens: 232 *)
Admitted.
Hint Extern 1 ({{_}} Bind (update_fblock_d _ _ _ _ _) _) => apply update_fblock_d_ok : prog.
Theorem file_sync_ok: forall fsxp inum mscs,
    {< ds sm Fm Ftop tree pathname f ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs')
      exists ds' sm' tree' al,
        [[ MSAlloc mscs = MSAlloc mscs' ]] *
        [[ MSCache mscs = MSCache mscs' ]] *
        [[ MSAllocC mscs = MSAllocC mscs' ]] *
        [[ MSIAllocC mscs = MSIAllocC mscs' ]] *
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
        [[ ds' = dssync_vecs ds al]] *
        [[ length al = length (DFData f) /\ forall i, i < length al ->
              BFILE.block_belong_to_file ilist (selN al i 0) inum i ]] *
        [[[ ds'!! ::: (Fm * rep fsxp Ftop tree' ilist frees mscs' sm')]]] *
        [[ tree' = update_subtree pathname (TreeFile inum  (synced_dirfile f)) tree ]] *
        [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                        ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} file_sync fsxp inum mscs.
Proof.
(* skipped proof tokens: 158 *)
Admitted.
Hint Extern 1 ({{_}} Bind (file_sync _ _ _) _) => apply file_sync_ok : prog.
Theorem tree_sync_ok: forall fsxp  mscs,
    {< ds sm Fm Ftop tree ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] 
    POST:hm' RET:^(mscs')
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (ds!!, nil)) (MSLL mscs') sm hm' *
      [[ MSAlloc mscs' = negb (MSAlloc mscs) ]] *
      [[ MSCache mscs' = MSCache mscs ]] *
      [[ MSICache mscs' = MSICache mscs ]] *
      [[ MSAllocC mscs' = MSAllocC mscs ]] *
      [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
      [[ MSDBlocks mscs' = MSDBlocks mscs ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} tree_sync fsxp mscs.
Proof.
(* original proof tokens: 58 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (tree_sync _ _) _) => apply tree_sync_ok : prog.
Theorem tree_sync_noop_ok: forall fsxp  mscs,
    {< ds sm Fm Ftop tree ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]]
    POST:hm' RET:^(mscs')
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[ MSAlloc mscs' = negb (MSAlloc mscs) ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} tree_sync_noop fsxp mscs.
Proof.
(* skipped proof tokens: 42 *)
Admitted.
Hint Extern 1 ({{_}} Bind (tree_sync_noop _ _) _) => apply tree_sync_noop_ok : prog.
Theorem lookup_ok: forall fsxp dnum fnlist mscs,
    {< ds sm Fm Ftop tree ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
      [[ dirtree_inum tree = dnum]] *
      [[ dirtree_isdir tree = true ]]
    POST:hm' RET:^(mscs', r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
      [[ (isError r /\ None = find_name fnlist tree) \/
         (exists v, r = OK v /\ Some v = find_name fnlist tree)%type ]] *
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]]
    CRASH:hm'  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
     >} lookup fsxp dnum fnlist mscs.
Proof.
(* skipped proof tokens: 123 *)
Admitted.
Hint Extern 1 ({{_}} Bind (lookup _ _ _ _) _) => apply lookup_ok : prog.
Theorem create_ok : forall fsxp dnum name mscs,
    {< ds sm pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
      [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ isError r ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]]
      \/ exists inum,
       [[ r = OK inum ]] * exists d tree' ilist' frees',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm' *
       [[ tree' = tree_graft dnum tree_elem pathname name (TreeFile inum dirfile0) tree ]] *
       [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
       [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                       ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]])
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d inum tree' ilist' frees' mscs',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
      [[ tree' = tree_graft dnum tree_elem pathname name (TreeFile inum dirfile0) tree ]] *
      [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
      [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                       ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
      [[ MSAlloc mscs' = MSAlloc mscs ]]
    >} create fsxp dnum name mscs.
Proof.
(* skipped proof tokens: 183 *)
Admitted.
Hint Extern 1 ({{_}} Bind (create _ _ _ _ ) _) => apply create_ok : prog.
Definition rename_rep_inner d frees' ilist' tree' srcnum srcents subtree pruned dstnum dstents renamed mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname
    : @pred addr addr_eq_dec valuset :=
    ([[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
    [[ find_subtree srcpath (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ]] *
    [[ find_dirlist srcname srcents = Some subtree ]] *
    [[ pruned = tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem) ]] *
    [[ find_subtree dstpath pruned = Some (TreeDir dstnum dstents) ]] *
    [[ renamed = tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
    [[ tree' = update_subtree cwd renamed tree ]] *
    [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                    ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
    [[ forall inum' def', inum' <> srcnum -> inum' <> dstnum ->
       In inum' (tree_inodes tree') ->
       selN ilist inum' def' = selN ilist' inum' def' ]])%pred.
Definition rename_rep ds mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname hm :=
    (exists d tree' srcnum srcents dstnum dstents subtree pruned renamed ilist' frees',
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm *
    rename_rep_inner d frees' ilist' tree' srcnum srcents subtree pruned dstnum dstents renamed mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname
    )%pred.
Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< ds sm Fm Ftop tree cwd tree_elem ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
      [[ find_subtree cwd tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
         ([[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] \/
      [[ ok = OK tt ]] * 
        rename_rep ds mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname hm')
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d tree' srcnum srcents dstnum dstents subtree pruned renamed ilist' frees' mscs',
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
      rename_rep_inner d frees' ilist' tree' srcnum srcents subtree pruned dstnum dstents renamed mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
Proof.
(* skipped proof tokens: 163 *)
Admitted.
Hint Extern 1 ({{_}} Bind (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.
Theorem delete_ok : forall fsxp dnum name mscs,
    {< ds sm pathname Fm Ftop tree tree_elem frees ilist,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
      [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs', ok)
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ isError ok ]] *
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
                [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] \/
      [[ ok = OK tt ]] * exists d tree' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm' *
        [[ tree' = update_subtree pathname
                      (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
        [[ forall inum def', inum <> dnum -> In inum (tree_inodes tree) ->
           In inum (tree_inodes tree') ->
           selN ilist inum def' = selN ilist' inum def' ]])
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d tree' ilist' frees' mscs',
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
      [[ tree' = update_subtree pathname
                    (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
      [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
      [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                      ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
      [[ forall inum def', inum <> dnum ->
           (In inum (tree_inodes tree') \/ (~ In inum (tree_inodes tree))) ->
          selN ilist inum def' = selN ilist' inum def' ]]
    >} delete fsxp dnum name mscs.
Proof.
(* skipped proof tokens: 153 *)
Admitted.
Hint Extern 1 ({{_}} Bind (delete _ _ _ _) _) => apply delete_ok : prog.
End AFS.
