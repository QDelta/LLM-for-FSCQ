Require Import Prog.
Require Import Log.
Require Import BFile.
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
Require Import AsyncFS.
Set Implicit Arguments.
Import ListNotations.
Module AFS_RECOVER.
Import AFS.
Import DirTree.
Import DirTreeDef.
Parameter cachesize : nat.
Axiom cachesize_ok : cachesize <> 0.
Hint Resolve cachesize_ok.
Notation MSLL := BFILE.MSLL.
Notation MSAlloc := BFILE.MSAlloc.
Theorem file_getattr_recover_ok : forall fsxp inum mscs,
  {X<< ds sm pathname Fm Ftop tree f ilist frees,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
         [[[ ds!! ::: (Fm * DirTreeRep.rep fsxp Ftop tree ilist frees mscs sm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
         [[ r = DFAttr f ]]
  REC:hm' RET:r exists mscs fsxp,
         exists d sm' n, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) sm' hm' *
         [[ n <= length (snd ds) ]] *
         [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
  >>X} file_get_attr fsxp inum mscs >> recover cachesize.
Proof.
(* original proof tokens: 197 *)

(* No more tactics to try *)
Admitted.

Theorem read_fblock_recover_ok : forall fsxp inum off mscs,
    {X<< ds sm Fm Ftop tree pathname f Fd vs ilist frees,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[[ ds!! ::: (Fm * DirTreeRep.rep fsxp Ftop tree ilist frees mscs sm)]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs', r)
           LOG.rep (FSXPLog fsxp) (SB.rep  fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
           [[ r = fst vs ]]
    REC:hm' RET:r exists mscs fsxp,
         exists d sm' n, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) sm' hm' *
         [[ n <= length (snd ds) ]] *
         [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
    >>X} read_fblock fsxp inum off mscs >> recover cachesize.
Proof.
(* original proof tokens: 198 *)

(* No more tactics to try *)
Admitted.

Lemma instantiate_crash : forall idemcrash (F_ : rawpred) (hm_crash : hashmap),
    (fun hm => F_ * idemcrash hm) hm_crash =p=> F_ * idemcrash hm_crash.
Proof.
(* original proof tokens: 11 *)
eapply pimpl_fun_l.
(* No more tactics to try *)
Admitted.

Hint Extern 0 (okToUnify (DirTreePred.tree_pred _ _) (DirTreePred.tree_pred _ _)) => constructor : okToUnify.
End AFS_RECOVER.
